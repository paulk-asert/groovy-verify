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
(`@Requires` / `@Ensures` / `@Invariant`), compile under

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

The engine proves these kinds of property at **compile time** — and when it can't, it **refutes with a concrete
counterexample** (Dafny/Verus-style) rather than passing silently:

- **Preconditions** — every `@Requires` is discharged at each call site.
- **Postconditions** — a method body is proved to satisfy its `@Ensures` on every path, including early returns.
- **Class invariants** — a `@Invariant` is established by construction and preserved by every mutator, so a whole
  data structure (a ring buffer, a bank account) verifies as a unit.
- **Loop invariants & termination** — a loop `@Invariant` is established and maintained, and `@Decreases` proves
  the loop *terminates* — the same measure turning a recursive call into proof by induction.
- **Memory & arithmetic safety** — array indices in bounds, dereferences non-null, divisors non-zero, and — opt-in
  — no integer overflow: the implicit obligations, discharged from the contracts in scope.
- **Rely/guarantee** — under concurrent interference each thread's steps uphold its `@Guarantee` while tolerating
  the others' `@Rely`, so a shared buffer stays in bounds without a lock.
- **Information flow** — no secret (`@Label('High')`) reaches a public sink (noninterference), with explicit
  `Declassify` for controlled release.
- **Behavioural subtyping (Liskov)** — an override may only *weaken* a precondition and *strengthen* a
  postcondition, never the reverse.
- **Algebraic laws** — a `@Reducer` combiner is proved to satisfy the monoid laws, and a `@Monadic` carrier the
  monad / functor laws — automatically, from the annotation alone.

The full per-capability table — each with a ✅ phase tag and its honest "deferred" edge — is in
**[CAPABILITIES.md](CAPABILITIES.md)**.

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
  and GString interpolation. *Rewriting* a string — `replace` / `replaceAll` / `toUpperCase` / `toLowerCase` /
  `reverse` — folds on **literal** strings (plus a few weak axioms, e.g. length-preservation), with no general
  symbolic algebra. *Out:* building a string char-by-char (use a `char[]`).
- **Collections & data** — arrays and lists (read, update, bounds), finite `Set` and `Map` (membership, mutation,
  cardinality, the full set algebra `∪ ∩ − ^`), `Tuple` / `TupleN` and Groovy's map-as-named-tuple returns,
  immutable factories, and a `.limit(n)` / `.take(n)`-bounded `every` / `any` over an infinite `Stream.iterate`
  (proven by induction over the prefix) — all reasoned over with bounded **universal *and* existential**
  quantifiers that nest. *Out:* `.keySet()` / `.values()` projection, nested-set mutation, and that same infinite stream
  `every` / `any` with no `.limit` (it never returns).
- **Control flow** — `if` / `else`; `while`, `do-while`, `for`, and `for (x in xs)` loops (optionally one level
  nested) with `@Invariant` / `@Decreases`; early `return`; and `switch` *expressions* — the arrow form
  (`case 1 -> …`) with literal / range labels; plus side-effecting assignment, `++` / `--`, and parallel swap.
  *Out:* `try` / `catch`, `.each`, the older colon-style `switch` *statement* (`case 1:` … `break`) and
  type-pattern cases (`case String s`); closures and lambdas appear only as specification predicates
  (`every` / `any` / `inject`) and as law-carriers (`@Monadic` / `@Reducer`).

**Spec sources** — beyond `@Requires` / `@Ensures` / `@Invariant`, a precondition can also be read off a Jakarta /
`javax.validation` constraint on a parameter or field — `@Positive`, `@Min` / `@Max`, `@Size`, `@NotEmpty` — so
code already annotated for *runtime* validation verifies as-is.

The full itemised enumeration — every operator, type, theory, phase, and honest boundary — is in
**[FRAGMENT.md](FRAGMENT.md)**. The worked examples below put it through its paces.

## Examples

Each snippet below is compiled under `@TypeChecked(extensions = 'verification.VerifyChecker')`,
so the proofs run at **compile time**. The contracts are stock `groovy.contracts`
annotations, so the same `@Requires`/`@Ensures`/`@Invariant` still execute as ordinary
runtime checks when verification is off.

Because the checker is a `@TypeChecked` *extension*, verification is opt-in per class or method:
prove the high-value parts, leave the rest as ordinary Groovy. The explicit annotation is optional
too — a compile-time customiser or config script can apply the extension across a whole source set,
removing the per-class `@TypeChecked`. And the economics fall where they should: for a verified
**library**, only the library's *own* compile bears the proof burden — its consumers run no Z3 and
write no specs, yet inherit the guarantees. Because each obligation the verifier can't discharge stays
an ordinary `groovy.contracts` assertion, a fragment limitation costs a *runtime* check rather than the
guarantee; and because groovy-contracts lets those runtime assertions be switched off (in a production
build, say), a consumer needn't pay even that. The proof is discharged once, at the library's compile
time — what survives a verifier limitation is a runtime contract, and what survives into production can
be nothing at all.

The examples build from the shape of a single proof to a fully verified algorithm — five acts, covering every kind of data Groovy code touches (arrays, lists, sets, maps, `BigDecimal`, IEEE-754 floats, objects, and graphs) in the idiom you'd already write.

### Act 1 — What a proof looks like

*The core machinery: a postcondition, a loop invariant with a termination measure, and the loop forms — closing on a property no test could ever check.*

**Postconditions — the contract is the spec.** Z3 proves the body satisfies `@Ensures`:

<!-- doclint:ignore README illustration: @Ensures on max -->
```groovy
@Ensures({ result >= a && result >= b })
static int max(int a, int b) { a >= b ? a : b }
```

Get the body wrong — return the *smaller* (`a >= b ? b : a`) — and the proof fails at compile
time with an input that breaks it:

```
[Static type checking] - Cannot prove postcondition of max holds on this return path
    ensured: ((result >= a) && (result >= b))
    counterexample: a = -1, b = 0
    fails on: max(-1, 0)
```

**Loop invariants & termination.** The two classic loop bugs — an off-by-one that computes the wrong
result, and a loop that never ends — are exactly what `@Invariant` and `@Decreases` rule out: the
invariant carries the proof across iterations and `@Decreases` (a measure that must strictly shrink)
shows the loop terminates, so the postcondition `result == n` is *proven of the computed value*, not
assumed. (Recursion works the same way — a method-level `@Decreases` lets the method's own `@Ensures`
be assumed at the recursive call: the proof-by-induction step.)

<!-- doclint:case regression-loop/countup-verified -->
```groovy
@Requires({ n >= 0 })
@Ensures({ result == n })
static int countUp(int n) {
    int i = 0
    @Invariant({ 0 <= i && i <= n })
    @Decreases({ n - i })
    while (i < n) { i++ }
    return i
}
```

The recursion that parenthetical mentions reads the same — a recursive `factorial` whose own `@Ensures`
is assumed at the recursive call (the induction hypothesis), proven to grow at least linearly:

<!-- doclint:case p-induction/compound-return-n-fact-n-1-call-hoisted -->
```groovy
@Requires({ n >= 1 })
@Ensures({ result >= n })          // factorial grows at least linearly — proven by induction on n
@Decreases({ n })
static int fact(int n) {
    if (n <= 1) return 1
    return n * fact(n - 1)         // the recursive call's @Ensures is the induction hypothesis
}
```

The base (`fact(1) == 1 >= 1`) closes directly; the step assumes `fact(n - 1) >= n - 1` and the defining
`fact(n) == n * fact(n - 1)` to reach `fact(n) >= n`. This same **proof-helper** idiom — a method that
exists to establish a fact by induction — does load-bearing work in Act 5 (the sort's `maxBound`, the
DFS's `bcount`).

**The accumulator form earns something extra — `@TailRecursive`.** Pass an accumulator and mark the
helper `@TailRecursive`, and Groovy rewrites the body into an iterative loop — so deep recursion runs in
constant stack instead of overflowing it. The proof is untouched by that rewrite: it reasons about the
*recursive* source the loop is derived from, hoisting the tail call to an implicit local bound by the
callee's `@Ensures` (the induction hypothesis), so the inductive contract still discharges:

<!-- doclint:ignore README illustration: @TailRecursive accumulator induction -->
```groovy
import groovy.transform.TailRecursive

@TailRecursive
@Requires({ n >= 0 && acc >= 1 })
@Ensures({ result >= acc })
@Decreases({ n })
static long factHelper(long n, long acc) {
    if (n <= 1) return acc
    long next = n * acc
    return factHelper(n - 1, next)      // tail call — reasoned about inductively, executed as a loop
}
```

Three guarantees from one piece of source: the contract is **proven** at compile time (induction on the
recursive form), the runtime is a **stack-safe loop** (the `@TailRecursive` rewrite), and the `@Ensures`
still **runs at runtime** — groovy-contracts inlines its check at the rewritten return, so the
executable-spec dual-tenet survives even after another AST transform has restructured the body.

> [!NOTE]
> **A Groovy aside — the loop `@TailRecursive` generates (the form the proof never sees).** The transform runs
> at `SEMANTIC_ANALYSIS`, *after* the verifier has snapshotted the body at `CONVERSION`, and rewrites the tail
> call into a reassign-and-loop so the runtime never grows the stack. Roughly:
>
> ```groovy
> static long factHelper(long n, long acc) {
>     while (true) {                     // @TailRecursive wraps the body in a loop
>         if (n <= 1) return acc
>         long next = n * acc
>         long _n = n - 1, _acc = next   // `return factHelper(n - 1, next)` becomes:
>         n = _n; acc = _acc             //   reassign the parameters to the call's arguments…
>         continue                       //   …and loop back, instead of recursing deeper
>     }
> }
> ```
>
> So the verifier proves the *recursive* form above (induction via `@Decreases`) while Groovy executes *this*
> form (constant stack). Same source, two readings — and it's exactly why the lock (`@WithWriteLock`) and rely
> (`@UnderRely`) transforms can be "transparent" in the same way: the contract and the clean body are captured
> *before* any of these transforms rewrite it, so each verifies the form you wrote, not the one that runs.

The same machinery handles **aggregation** — and running totals are a classic source of *silently
wrong* answers (an off-by-one or a forgotten element yields a plausible-but-wrong number, with no
exception to flag it). Here the loop invariant carries a *prefix sum* `xs[0..<i].sum()` (the idiomatic
Groovy spelling), so the returned value is *proven* equal to the whole-list sum:

<!-- doclint:ignore README illustration: loop-invariant running sum -->
```groovy
@Requires({ xs != null && xs.size() > 0 })
@Ensures({ result == xs.sum() })
static int total(List<Integer> xs) {
    int s = xs[0]
    int i = 1
    @Invariant({ 1 <= i && i <= xs.size() && s == xs[0..<i].sum() })
    @Decreases({ xs.size() - i })
    while (i < xs.size()) { s += xs[i]; i++ }
    return s
}
```

Under the hood the solver is told just two facts about `sum` — the sum of an empty range is `0`, and
extending a range by one element adds that element — which is exactly enough to prove the body's
`s = s + xs[i]` keeps `s == xs[0..<i].sum()` true on every iteration. (The non-empty guard reflects a
real Groovy semantic: `[].sum()` is `null`, not `0`.)

**Loops aren't just `while` — `for`/`for-in`, with per-element invariants.** A `for (x in xs)` iterates the
collection directly, and its `@Invariant` can carry *two kinds* of clause at once: an ordinary **accumulator**
clause checked at the loop head (`s >= 0`), and a **per-element** clause checked at body-entry with `x` bound
to the current element (`x >= 0`) — exactly the per-element check groovy-contracts runs at runtime. Here the
element clause discharges straight from the precondition `xs.every { it >= 0 }`, and together they prove the
running total never goes negative:

<!-- doclint:ignore README illustration: for-in non-negative sum -->
```groovy
@Requires({ xs.every { it >= 0 } })
@Ensures({ result >= 0 })
static int sumAll(List<Integer> xs) {
    int s = 0
    @Invariant({ s >= 0 && x >= 0 })
    for (x in xs) { s += x }
    s
}
```

The per-element clause is correctly **vacuous on an empty collection** — the body never runs, so a clause that
couldn't be proven of an arbitrary element still verifies when the precondition forces `xs` empty (fixing a
false positive the old loop-head check hit on the never-iterated case). Classic `for (i = 0; i < n; i++)` and
the Java-style `for (int x : xs)` lower through the same machinery. (For *index*-arithmetic invariants like the
prefix-sum `xs[0..<i].sum()` above, reach for `while`/`for(;;)` — the for-in's iteration index is synthesised
and not in scope; for-in's strength is exactly this **per-element** reasoning.)

**A property you can't even test — proven anyway.** `Stream.iterate(seed, f)` is *infinite*: a true
`.every { … }` over it never returns, so this is a contract you fundamentally cannot unit-test. Because the
spec stays **dual** (it also runs at runtime via groovy-contracts), a `.limit(n)` is required so the runtime
check terminates — but the verifier proves the property for *every* element, by the very base-case +
preservation step the loops above use (`P(seed)` and `∀x. P(x) ⟹ P(f(x))`):

<!-- doclint:ignore README illustration: bounded-stream .every -->
```groovy
@Requires({ n >= 0 })
@Ensures({ Stream.iterate(0, { k -> (k + 1) % 10 }).limit(n).every { int v -> v >= 0 && v < 10 } })
static void wheel(int n) { }
```

A literal `.limit(10)` would instead **unroll** to the exact ten-element conjunction the runtime spot-checks;
a *symbolic* `.limit(n)` like this one proves it for **all** elements — so the `(k + 1)` here is proven to
*never overflow*, a fact about the two-billionth element that no test could reach. The honesty cuts both ways:
a monotone `iterate(0){ k + 1 }` counter has *no* finite bound, so a `< 1_000_000` claim is **refused** rather
than silently accepted, and a terminal `.every` with no `.limit` at all **skips loudly** instead of blessing a
contract that would hang at runtime.

### Act 2 — Bugs the compiler now catches

*Bounds, null, and divide-by-zero are implicit obligations — no annotation needed, each refuted with a counterexample and a runnable repro; width-aware integer overflow is one annotation away.*

**Bugs caught at compile time — with a counterexample and a runnable repro.** The implicit
safety obligations (bounds, divide-by-zero, null) need no annotation; an access the checker
can't prove safe fails the build the way the JVM would name it, plus an input that triggers it:

<!-- doclint:case p1-bounds/unguarded-index-refuted -->
```groovy
static int g(int[] a, int i) { a[i] }   // index never checked
```
```
[Static type checking] - Possible IndexOutOfBoundsException: index may be out of bounds
    obligation: 0 <= i && i < a.size()
    counterexample: a.size() = 0, i = -1
    fails on: g(new int[0], -1)
```

The headline mirrors the exception a developer would actually hit
(`ArithmeticException: Division by zero`, `NullPointerException: Cannot invoke method
size() on null object`, …); the `fails on:` line reconstructs a runnable input — scalars
and a null receiver exact, solver-constrained array elements pinned as literals
(`diff([21239, 21238] as int[], 0)`), contents that don't matter left size-filled
(`new int[3]`).

**That counterexample isn't just a message — it feeds three tools.** The same `fails on:` line can be rendered as
a runnable repro test, turned into the `@Requires` that would discharge it, and — on the obligations that *pass* —
queried for which clauses the proof leaned on. These are opt-in environment knobs (`VERIFY_REFUTATION`,
`VERIFY_SUGGEST`, `VERIFY_EXPLAIN`), each leaving the default path untouched; they're collected under
[Tool knobs](#tool-knobs) below.

**Safe navigation carries the non-null fact.** A precondition `recv?.foo()` can only be truthy when `recv`
is non-null — Groovy's `?.` evaluates to `null` (falsy) on a null receiver — and the verifier reads that
implication, so an unguarded `recv.bar()` in the body discharges its null check with no redundant
`recv != null`:

<!-- doclint:case p97-safe-nav-non-null/titlelen-via-safe-nav-precondition-proves -->
```groovy
@Requires({ name?.startsWith("Dr. ") })          // ?. ⟹ name != null
@Ensures({ result >= 4 })
static int titleLen(String name) { name.length() }   // ✓ no NPE obligation left open
```

It stays sound by reading the implication only from a top-level `&&` conjunct: weaken the precondition to
`name?.startsWith("Dr. ") || name == null` and `name` can still be null, so the `name.length()` correctly
fails with the `NullPointerException` obligation again.

**Bounded integer overflow — Verus-style precision when you want it.** Anything in the fragment is
encoded as Z3's mathematical (unbounded) Int by default — the experience that makes most existing
proofs work. Methods (or classes) that annotate `@CheckOverflow` opt into a stronger guarantee:
every `+`, `-`, `*` becomes an implicit obligation that the math result stays in the operand type's
signed range, refuted otherwise with a runnable repro:

<!-- doclint:case p44-overflow/unguarded-increment-refutes -->
```groovy
class C {
    @CheckOverflow
    static int incr(int n) { n + 1 }                  // refutes
}
```

```
Possible ArithmeticException: addition overflows 32-bit signed range
    obligation: Integer.MIN_VALUE <= (n + 1) && (n + 1) <= Integer.MAX_VALUE
    counterexample: n = 2147483647
    fails on: incr(2147483647)
```

Add `@Requires({ n < Integer.MAX_VALUE })` and it verifies. Sub-expression aware: `(a + 1) * (a + 1)`
generates an obligation for the inner add and one for the outer multiply, so an unguarded
square-of-successor refutes at the multiplication step with a sqrt(INT_MAX)-territory
counterexample.

The bound is **width-aware**: it follows Java binary numeric promotion of the operands, so a
`long`/`Long` operand widens the check to `[Long.MIN_VALUE, Long.MAX_VALUE]`. `@CheckOverflow long f(long n) { n + 1 }`
refutes only at the true 64-bit boundary (`n == Long.MAX_VALUE`) and verifies under `n < Long.MAX_VALUE` —
not a spurious 32-bit refute. `BigInteger` operands carry no obligation — unlike `int`/`long`, the
default unbounded model is *runtime-exact* for `BigInteger`, which never overflows. Where the `int` version
above needs `@CheckOverflow` and a bound, the `BigInteger` sum is proven for *all* non-negative inputs, however
large, with no guard at all:

<!-- doclint:case p124-biginteger/addition-verifies-unbounded-int -->
```groovy
class C {
    @Requires({ a >= 0 && b >= 0 })
    @Ensures({ result == a + b })
    static BigInteger add(BigInteger a, BigInteger b) { a + b }
}
```

(`BigInteger` is Z3's unbounded `Int` sort exactly — the most faithful integer type, since `Int` carries no
width — and a literal like `42g` folds too, modulo one wider than 64 bits, which skips loudly.)

Method-level math-int reasoning (no annotation) is preserved verbatim — the entire existing test
suite continues to verify unchanged, and the permutation-sort showcase still uses the unbounded
`int[].count(v)`. `@CheckOverflow` is **additive**: it puts groovy-verify in the same
machine-integer-precision territory as Verus or Dafny without forcing the typed-narrow ergonomic
that limits adoption — *math by default, machine precision on demand.*

### Act 3 — Whatever your data is

*One idiom across arrays, lists, sets, and maps — and three number models (math `int`, exact `BigDecimal`, IEEE-754 `double`) — proving the property in the spelling you'd already write.*

**Properties over whole arrays — in the idiom you'd already write.** This is how you turn a *latent*
assumption like "this method only works on a sorted array" into one the compiler enforces — so passing
unsorted input is a build error, not a surprise at runtime. The contract is a plain `.every { … }`
(a "for all" over the elements); a *sorted* precondition (every element ≤ its successor) lets the
checker conclude adjacent elements are ordered, and because it's ordinary GDK Groovy it runs as a
runtime check too:

<!-- doclint:ignore README illustration: sorted-adjacent difference -->
```groovy
@Requires({ (0..<a.length - 1).every { a[it] <= a[it + 1] } && 0 <= k && k + 1 < a.length })
@Ensures({ result <= 0 })
static int diff(int[] a, int k) { a[k] - a[k + 1] }
```

Drop the `every { … }` precondition and the claim no longer holds — and the counterexample is
a concrete array, with the offending elements reconstructed (here a decreasing adjacent pair):

```
[Static type checking] - Cannot prove postcondition of diff holds on this return path
    ensured: (result <= 0)
    counterexample: a.length = 2, k = 0
    fails on: diff([21239, 21238] as int[], 0)
```

For a property over the *whole* index range there's an even shorter spelling — `a.indices` **is** `0..<a.length`,
so "every element is non-negative" reads `a.indices.every { a[it] >= 0 }`, and that precondition is enough to
prove the in-range access `a[k]` yields a non-negative result:

<!-- doclint:case p9-native-quantifiers/indices-every-entails-instance -->
```groovy
@Requires({ a.indices.every { a[it] >= 0 } && 0 <= k && k < a.length })
@Ensures({ result >= 0 })
static int get(int[] a, int k) { a[k] }
```

**Building arrays — literals and sized allocation.** A method may construct and return an array. A
fixed-arity literal `new int[]{a, b}` (or a list literal `[a, b]` coerced to the `int[]` return) folds its
elements; a sized `new int[n]` is a fresh, Java-zero-filled array, so an unwritten slot reads `0` and a body
store bounds-checks against the length:

<!-- doclint:case readme-examples/singleton-sized-array-symbolic-n -->
```groovy
@Requires({ n >= 1 })
@Ensures({ result.length == n && result[0] == x })
static int[] singleton(int n, int x) {
    int[] r = new int[n]        // length n, all zero
    r[0] = x
    return r
}
```

`result.length == n` proves from the allocation, `result[0] == x` from the store; a store past the length
(`r[n] = x`) refutes with an `IndexOutOfBounds` repro.

**`++`/`--` in expression position — the array-copy idiom.** A side-effecting `i++` used *inside* an
expression is supported — the classic two-cursor copy `dst[j++] = src[i++]` verifies. Each inc/dec is hoisted
to its value plus the increment, so the loop invariant carries the copied prefix and the whole copy is proven
element-for-element:

<!-- doclint:case readme-examples/two-cursor-array-copy-dst-j-src-i -->
```groovy
@Requires({ src != null && dst != null && src.length <= dst.length })
@Ensures({ (0..<src.length).every { result[it] == src[it] } })
static int[] copy(int[] src, int[] dst) {
    int i = 0, j = 0
    @Invariant({ 0 <= i && i <= src.length && i == j && (0..<i).every { dst[it] == src[it] } })
    @Decreases({ src.length - i })
    while (i < src.length) { dst[j++] = src[i++] }   // dst[j] = src[i]; i++; j++
    return dst
}
```

The store's bounds discharge from the invariant and `src.length <= dst.length`, and both cursors advance each
pass. The single-index form `dst[i] = src[i++]` verifies too: `i` appears twice, but the verifier checks
**evaluation order** — Java evaluates the LHS index before the right-hand side, so the `i` in `dst[i]` reads
the *old* value just as the hoisted-after `i++` does. What it refuses is a variable read *after* its own
increment — `x = i++ + i`, where Java advances `i` mid-statement so the second `i` is the new value — which
skips loudly rather than risk mis-modeling.

**Lists and boxed types — same reasoning, same syntax.** The encoder never inspects whether a value
is `int` or `Integer`, or whether a sequence is an `int[]` or a `List` — it models every integer type
as a mathematical integer and any subscripted, sized receiver as its contents. So `max` above proves
identically declared `Integer max(Integer a, Integer b)`, and the sorted-`diff` holds verbatim over a
`List<Integer>`, in the same idiom (`xs[i]`, `xs.size()`):

<!-- doclint:case boxed-list/list-integer-sorted-diff-verified -->
```groovy
@Requires({ (0..<xs.size() - 1).every { xs[it] <= xs[it + 1] } && 0 <= k && k + 1 < xs.size() })
@Ensures({ result <= 0 })
static int diff(List<Integer> xs, int k) { xs[k] - xs[k + 1] }
```

A `List<String>` index is bounds-checked the same way — the element type is irrelevant to the access.
And the *element* itself is now nullity-checked: calling a method on `xs[i]` (or `xs.get(i)`) raises
an obligation to prove the element non-null — the verifier tracks a per-element nullity flag — which
an `@Requires` or an `if` guard discharges, and which is otherwise refuted with a `fails on: f([null])`
repro (the input that triggers the NPE):

<!-- doclint:ignore README illustration: list-element non-null guard -->
```groovy
@Requires({ xs.size() > 0 && xs[0] != null })
static int firstLen(List<String> xs) { xs[0].length() }
```

Drop the `xs[0] != null` guard and the refutation pins a concrete failing input. The Java-style
method idioms `xs.get(i)` / `xs.first()` / `xs.head()` / `xs.last()` / `xs.set(i, v)` lower
through the same array-access machinery (with the bounds check synthesised so `xs.first()` on a
possibly-empty list refutes with `fails on: f([])` exactly as `xs[0]` would). Size-changing
mutation — `xs.add(v)`, `xs.removeLast()` / `xs.pop()`, `xs.clear()` — threads the size and
contents oracles in **static-single-assignment** (SSA) form — each write mints a fresh name, so a
mutator's pre- and post-states stay distinct — and pairs with a runtime-faithful `xs.count(v)` (see the
"Lists — mutation" beat below); only the shift-based variants (`xs.add(i, v)`, `xs.remove(i)`)
still defer. Immutable-container factories (`List.of(...)`, `[a, b, c]`, `Map.of`, …) **are** in,
peephole-folding to ground SMT terms on `.size()`, `.contains`, `.get(literal_i)`, and the same
folds lift across a local: `xs = List.of(1, 2, 3); xs[1]` proves `result == 2`.

**String-keyed sets and maps, with the same machinery.** Sets and maps work over `Set<Integer>` /
`Map<Integer,Integer>` and likewise over `Set<String>` / `Map<String,Integer>` (and the enum
variants), the only change being the element sort the encoder uses — every contract idiom
(`x in s`, `s.size()`, `m["k"]`) reads the same. The cardinality law carries across: a fresh-element
add raises the size by one, refuted if the add isn't fresh:

<!-- doclint:ignore README illustration: set-mutation @Modifies frame -->
```groovy
class Acl {
    Set<String> admins
    @Requires({ !("root" in admins) })
    @Modifies({ this.admins })
    @Ensures({ "root" in admins && admins.size() == old.admins.size() + 1 })
    void grantRoot() { admins.add("root") }
}
```

Drop the `!("root" in admins)` precondition and the `+ 1` refutes — adding a key that's already
present is a no-op, and the verifier names exactly the postcondition that fails:

```
[Static type checking] - Cannot prove postcondition of grantRoot holds on this return path
    ensured: ((root in admins) && (admins.size() == (old.admins.size() + 1)))
```

Same machinery, real-world types. For a method with a String or Enum parameter, the verifier
additionally renders a `fails on: grant("…")` / `fails on: paint(Color.RED)` line — pinning the
refuting parameter from the model as a Groovy literal — just as it does for the int-parameter
examples above.

**Permissions — `Map<Role, Set<Perm>>` nested element domains.** Sets compose with maps the way a
typical RBAC table is written: each role maps to a set of granted permissions, looked up by `m[k]`.
The map's *value sort* is the inner set's characteristic-array sort `Array<Perm, Int>`, so `m[k]`
reads as a transient set; `m[k].contains(p)` is membership, and `m[k].containsAll(required)`
finite-conjuncts over the inner enum's constants. So a covering-implies-granted claim is a one-liner:

<!-- doclint:case p36-nested-map-set/readme-rbac-adminmaywrite-verifies -->
```groovy
class Acl {
    enum Role { ADMIN, USER, GUEST }
    enum Perm { READ, WRITE, DELETE }
    @Requires({ grants[Role.ADMIN].containsAll(required) })            // ADMIN covers required …
    @Ensures({ (Perm.WRITE in required) ==> (Perm.WRITE in grants[Role.ADMIN]) })   // … so WRITE, when requested, is held
    static int adminMayWrite(Map<Role, Set<Perm>> grants, Set<Perm> required) { 0 }
}
```

The verifier closes the gap between "ADMIN covers `required`" and "WRITE is in `grants[ADMIN]` whenever
`WRITE ∈ required`" via the per-constant conjunction over `Perm`. Drop the `containsAll` precondition
and the postcondition rightly refutes: without coverage, the requested permission isn't pinned in
the admin's grant set. Inner-set mutation (`grants[k].add(p)`) and `grants[k].size()` are out of the
read-only nesting fragment today.

**Set algebra — union, intersection, difference, symmetric difference.** All of Groovy's set operators
verify, with both the operator and method spellings: `a + b` / `a | b` / `a.or(b)` (union),
`a & b` / `a.and(b)` / `a.intersect(b)` (intersection), `a - b` (difference) and `a ^ b` (symmetric
difference, "in exactly one"). A method that **returns** a set can spec its `result` member-by-member —
so a policy merge proves it's exactly the union, characterised at an arbitrary element `p`:

<!-- doclint:case p35b-set-return/readme-union-result-granted-extra -->
```groovy
@Requires({ granted != null && extra != null })
@Ensures({ (p in result) == (p in granted || p in extra) })   // result == granted ∪ extra
static Set<Integer> merge(Set<Integer> granted, Set<Integer> extra, int p) { granted | extra }
```

`p in result` folds to the inline union membership `p in granted || p in extra` (the verifier binds a
set-binop `result` to its definition), and because `p` is an unconstrained parameter, proving the
equivalence for `p` proves it for *every* element. The element-wise lowering keeps it honest: returning
`granted & extra` (intersection) under the same `@Ensures` rightly refutes, and `p in a` alone does **not**
entail `p in (a ^ b)` — `p` might be in `b` too, so symmetric difference excludes it. (One Groovy wrinkle:
`a.intersect(b)` returns a `Collection`, so a `Set`-typed result wants the operator `a & b` / `a.and(b)`,
which return a `Set`.) The `containsAll` and materialised forms (`Set u = a + b`, then `u.containsAll(a)`)
work over enum-element sets (finite domain) and Int-element sets under a `Sets.boundedBy` bound.

**State machines — every state handled, machine-checked.** A `Set<State>` over an `enum` has a
finite domain the verifier exploits: the pigeonhole `handled.size() <= 3` is automatic for any
`Set<State>` (a 3-state enum), and the iff `Sets.boundedCount(handled, N) == N ⟺ every enum constant ∈
handled` is asserted on the set's first use. So an FSM-completeness claim becomes a one-line
contract:

<!-- doclint:case p29-enum-sets/fsm-via-set-state-full-coverage-entails-every-state -->
```groovy
class FSM {
    enum State { IDLE, RUNNING, DONE }
    Set<State> handled
    @Requires({ Sets.boundedCount(handled, State.values().length) == State.values().length })
    @Ensures({ State.IDLE in handled && State.RUNNING in handled && State.DONE in handled })
    boolean allHandled() { true }
}
```

Drop the `@Requires` and the postcondition rightly refutes — partial coverage can't entail
every state. No ordinals, no workaround — the direct `Set<State>` spelling composes the enum
literal interning, the `State.values().length` constant-folding, and the enum-domain
pigeonhole + full-coverage iff into a single proof.

**Arithmetic that matches Groovy — including the surprises.** Two things here trip up real code.
First, **`/` on integers is `BigDecimal` division in Groovy** — `5 / 2 == 2.5`, not `2` — so the
verifier models it that way and won't pretend a spec assuming `5 / 2 == 2` is correct (integer
division is `a.intdiv(b)` or `(int)(a / b)`). Second, *variable* multiplication (`a * b` where
neither side is a constant) is now handled by Z3's non-linear integer arithmetic (NIA), so sign facts
(`i * i >= 0`), divisibility (`n % 2 == 0`), and bounded products verify directly:

<!-- doclint:ignore README illustration: square-in-bounds + div/mod round-trip -->
```groovy
// Bounded squaring — the prime-testing bound check that previously hit the opt-out.
@Requires({ 0 <= i && i <= 100 })
@Ensures({ result <= 10000 })
static int squareInBounds(int i) { i * i }

// Integer division/modulo, modelled on Groovy's *actual* semantics: intdiv truncates toward
// zero, % is the sign-of-dividend remainder. The round-trip identity holds for every non-zero b.
@Requires({ b != 0 })
@Ensures({ result == a })
static int divModRoundTrip(int a, int b) { a.intdiv(b) * b + (a % b) }
```

The division/modulo handling follows **Groovy**, not Java (they differ): `/` on integers is
*`BigDecimal`* division (`5 / 2 == 2.5G`), now modelled with Z3's exact-real arithmetic so a spec
over it is *proven* — `a / 2 == 2.5` verifies and `a / 2 == 2` refutes, and a `BigDecimal` average is
provably `(a + b) / 2` (genuine integer division is `a.intdiv(b)` or `(int)(a / b)`, truncating toward
zero, modelled distinctly). `%` and `.remainder(b)` are the
sign-of-dividend remainder (`-5 % 2 == -1`); `.mod(b)` is `BigInteger.mod` (non-negative, and the
verifier adds the Groovy-specific obligation that the modulus is `> 0`). The implicit `b != 0`
obligation still fires on division/`intdiv`/`%` by zero, refuting with a runnable repro. Hard NIA
corners (general polynomial identities for symbolic-signed operands, square-root / factoring shapes)
can time out — Z3 returns UNKNOWN and the verifier surfaces "Could not decide," never a silent pass.

**Bitwise and shift operators — at Java's 32-bit width.** `& | ^ << >> >>>` and complement `~` are modelled faithfully. A shift by a
literal is power-of-two arithmetic (`x << 1 == x * 2` proves), and a *low-bit mask* folds to arithmetic too —
`a & (2^k − 1)` is exactly `a mod 2^k` — so the low bit of any `int` is `0` or `1`:

<!-- doclint:case readme-examples/lowbit-bitwise-low-bit -->
```groovy
@Ensures({ result == 0 || result == 1 })
static int lowBit(int a) { a & 1 }
```

A non-mask `& | ^` (`a ^ a == 0`, `a & a == a`) goes through Z3's bit-vector theory, so two's-complement facts
hold exactly: `6 & 3 == 2` proves, a wrong concrete value (`6 & 3 == 3`) refutes. That reasoning is bit-blasted,
so a *false symbolic* claim soft-fails to a loud "could not decide" rather than a counterexample — sound, never
a false pass.

**A bit-twiddling trick proven against an arithmetic spec — the OpenJML benchmark.** The
[OpenJML BitVectors tutorial](https://www.openjml.org/tutorial/BitVectors) builds to rounding a number up to the
next multiple of 16 with `n + ((-n) & 0x0f)` — a body that's pure bit manipulation, a spec that's pure
arithmetic. groovy-verify proves it:

<!-- doclint:case p103-mask-as-mod/openjml-round-up-to-16-proves-range-mod16 -->
```groovy
@Requires({ n <= 0x7ffffff0 })
@Ensures({ n <= result && result <= n + 15 && result % 16 == 0 })
static int roundUp(int n) { n + ((-n) & 0x0f) }
```

Because the low-bit mask `(-n) & 0x0f` becomes the arithmetic `(-n) mod 16`, the whole thing stays in linear
integer arithmetic and bridges to the spec's `+`, `%`, and `≤`: the `result % 16 == 0` divisibility goes through
where a bit-vector `&` would time out. A wrong spec is still caught — `result % 16 == 8` refutes with
`n = Integer.MIN_VALUE`. This is the OpenJML insight made concrete: an arithmetic specification, a bit-trick
body, bridged so the caller never pays the bit-vector cost.

**Shift equals power of two — proven for a whole range, not spot-checked.** Where a test would write
`(0..10).each { n -> assert (1 << n) == (2 ** n) }`, the verifier proves the identity for *every* `n` in the
range at once — the `**` recurrence axioms meet the bit-vector shift:

<!-- doclint:case p-shift-power/shift-equals-power-of-two-1-n-2-n-for-n-in-0-30 -->
```groovy
@Requires({ n >= 0 && n <= 30 })
@Ensures({ (1 << n) == (2 ** n).intValue() })
static void shiftIsPowerOfTwo(int n) {}            // ✓ holds for all 31 values
```

`n <= 30` is the *genuinely-true* range, not a solver limit: at `n >= 31` the 32-bit `1 << n` wraps negative
(`1 << 31 == -2147483648`) while `2 ** n` is an unbounded `BigInteger` (`2 ** 31 == 2147483648`), so they
really differ — and the verifier correctly declines to prove it there. Drop the guard, or change the equality
to an off-by-one, and it no longer verifies.

**Complement and unsigned shift — `~` and `>>>`.** The complement `~x` is the two's-complement identity
`-x - 1`, so it stays in plain integer arithmetic — fully symbolic, never refute-hostile:

<!-- doclint:case p125-complement-ushr/complement-identity-x-x-1 -->
```groovy
@Ensures({ result == -x - 1 })
static int comp(int x) { ~x }
```

The unsigned right shift `>>>` zero-fills from the left (where the arithmetic `>>` sign-fills), so its result is
always non-negative — and the bit-vector proves it for *every* `int`:

<!-- doclint:case p125-complement-ushr/unsigned-shift-is-always-non-negative -->
```groovy
@Ensures({ result >= 0 })
static int ushr(int x) { x >>> 1 }
```

The same `@Ensures({ result >= 0 })` on the arithmetic `x >> 1` correctly **refutes** (`-4 >> 1 == -2`) — exactly
the distinction `>>>` exists to make.

**Money — conservation, and no fractional cents.** Financial code lives on `BigDecimal`, and the proofs
that matter are about *value not leaking*. `BigDecimal` `+`/`-`/`*` are exact and Z3's Real sort models
exact arithmetic, so a conservation invariant is a *faithful* proof — and it isn't vacuous: skim a cent and
the build fails.

<!-- doclint:case p68-financial/transfer-conserves-total-no-money-lost -->
```groovy
class Bank {
    BigDecimal alice, bob
    @Requires({ amt >= 0.0 && amt <= alice })
    @Ensures({ alice + bob == old.alice + old.bob })          // no money is lost in the transfer
    void transfer(BigDecimal amt) { alice = alice - amt; bob = bob + amt }
}
// Change the body to `bob = bob + amt - 0.01` — a salami slice — and the @Ensures REFUTES.
```

For *rounding* — "no fractional cents syphoned in an interest or trade calculation" — model money as
integer minor units (cents), where the framework is strongest: the credited (floored) amount plus the
retained remainder equals the exact value, so nothing vanishes; and a calc claiming it credits the *exact*
amount is refuted whenever a remainder exists.

<!-- doclint:case p68-financial/interest-credits-every-cent-round-trip -->
```groovy
@Requires({ principal >= 0 && rateNum >= 0 && rateDen > 0 })
@Ensures({ result * rateDen + (principal * rateNum) % rateDen == principal * rateNum })  // every cent accounted for
static int interestCents(int principal, int rateNum, int rateDen) { (principal * rateNum).intdiv(rateDen) }
```

The same conservation scales to a *dynamic* `List<BigDecimal>` of balances — a per-store sum law makes the
two compensating sides of a transfer cancel, so `accounts.sum() == old.accounts.sum()` ("the books
balance") is proven. One honest edge: Z3 Real models exact `BigDecimal` *arithmetic* faithfully but not
*rounding* (`setScale`) — the other reason integer minor units are the soundest money model.

**The same sum, two number models — both proven.** `BigDecimal` is exact decimal; `double` is IEEE-754.
The checker models each *faithfully* — `BigDecimal` on Z3's exact-real arithmetic, `double` on Z3's
floating-point theory (bit-exact: round-nearest-even — RNE, NaN, ±∞) — so it proves the famous discrepancy
rather than papering over it:

<!-- doclint:ignore README illustration: BigDecimal vs IEEE-754 double -->
```groovy
@Ensures({ result == 0.3 })   static BigDecimal exact() { 0.1 + 0.2 }    // verified — 0.1 + 0.2 IS 0.3
@Ensures({ result != 0.3d })  static double    ieee()  { 0.1d + 0.2d }  // verified — 0.1d + 0.2d is NOT 0.3d
```

For `double`, the high-value proofs are **no-NaN / finiteness** — `Double.isFinite(x) ⟹ !Double.isNaN(x + x)`
verifies, and over `Math.sqrt`/`Math.abs` too (Z3's `fp.sqrt`/`fp.abs`): `x >= 0 ⟹ !Double.isNaN(Math.sqrt(x))`
is proven, while *unguarded* `Math.sqrt(x)` can be NaN (refutes). It's sound where exact reasoning isn't:
`(a + b) - b == a` *refutes* (FP isn't associative), `x == x` *refutes* (a NaN isn't equal to itself). Z3
**bit-blasts** FP (expands each operation to a Boolean circuit over the 64 bits), so it's straight-line and
timeout-gated — loops, the other transcendentals (`sin`/`exp`/…),
and tight error bounds stay out of the fragment.

### Act 4 — Change, tracked soundly

*Mutation under a sound frame: object fields valid by construction, the aliasing bug value-semantics tools miss, what `old` is for, and count-preserving collection updates.*

**Object state — instance fields, valid by construction.** Not just static functions: a method may
read and update its receiver's fields, and the checker threads field state across the write (so
the contract's entry `count` and exit `count` are different values, related by the assignment).
A class invariant declares the bound once — every constructor proves it *at exit* (the receiver
is valid by construction), and every method assumes it at entry and re-proves it at exit:

<!-- doclint:ignore README illustration: Counter class-invariant lifecycle -->
```groovy
@Invariant({ count >= 0 && count <= max })
class Counter {
    int count, max
    @Requires({ m > 0 })
    Counter(int m) { max = m }                  // establishes the invariant
    @Requires({ count < max })
    void increment() { count = count + 1 }      // maintains it
}
```

Int fields default to `0` at constructor entry (matching JVM semantics), so the constructor starts
with `count = 0`, and the `@Requires({ m > 0 })` lets the invariant's `0 <= max` close. Drop the
`@Requires` and the constructor refutes — with a runnable repro:

```
[Static type checking] - Cannot prove class invariant of <init> holds at method exit
    invariant: ((count >= 0) && (count <= max))
    counterexample: count = 0, m = -1, max = 0
    fails on: <init>(-1)
```

**One honest edge:** if a method's loop *mutates* a field the class invariant constrains, the loop's
preservation check still assumes that invariant about the very field being changed — sound only when
the loop body leaves invariant-referenced fields alone, so until a per-loop frame analysis (the
`@Modifies` analogue for loops) tightens it, keep actively-mutated state in the loop's own
`@Invariant` rather than relying on the class one.

A postcondition can relate the *exit* state to the *entry* state with `old` — `@Ensures({ count
== old.count + 1 })` — and `old` reaches into array contents too, which is how a method frames what
it leaves alone: a setter that touches only `a[j]` proves every *other* element is unchanged, which
reads naturally as an implication using Groovy 5's `==>` operator —
`@Ensures({ (0..<a.length).every { it != j ==> a[it] == old.a[it] } })` (groovy-contracts clones the
field for `old`, so this holds at runtime as well as in the proof). The `==>` operator and the
equivalent `.implies()` method both lower to `!a || b`; the older spelling `it == j || a[it] ==
old.a[it]` works too.

**Aliasing — the bug value-semantics tools miss.** When two references can point at the *same* object, a write
through one is visible through the other — something lightweight checkers ignore by treating distinct names as
distinct objects. This method *looks* obviously correct:

<!-- doclint:case p89-field-write/setboth-refuted-under-aliasing-forgot-a-b -->
```groovy
@Ensures({ a.balance == 100 && b.balance == 200 })
static void setBoth(Account a, Account b) { a.balance = 100; b.balance = 200 }
```

but the verifier **refuses** it — because if `a` and `b` are the *same* account, the second write wins and
`a.balance` ends at `200`, not `100`:

```
[Static type checking] - Cannot prove postcondition of setBoth holds on this return path
    ensured: ((a.balance == 100) && (b.balance == 200))
    counterexample: a$id = 3, b$id = 3      // same identity ⇒ a and b are the same object
```

Adding the distinctness precondition — Groovy's identity operator `!==` — makes it verify:

<!-- doclint:case p89-field-write/setboth-verifies-with-a-b -->
```groovy
@Requires({ a !== b })
@Ensures({ a.balance == 100 && b.balance == 200 })
static void setBoth(Account a, Account b) { a.balance = 100; b.balance = 200 }
```

Under the hood, two parameters of the same class are modelled as a per-field map indexed by object *identity*,
so `a === b` / `a.is(b)` (and `!==`) is identity equality and a write through `a` is seen through `b` exactly
when they alias. *(Straight-line `int` fields today; the natural `transfer` with `from.balance ==
old(from.balance) - amt` is deliberately out — groovy-contracts' `old` snapshots only `this`'s own fields, not
a parameter's, so that contract couldn't **also run** at runtime, and an executable spec is the whole point.)*

**Swap — and what `old` is for.** The textbook spec for a swap says "the result has the two inputs
exchanged" — and there are two faithful ways to write it, whose difference is the whole lesson. Mark the
parameters `final` and swap two **locals** instead: the parameters *can't* be reassigned, so they keep their
entry values, and the postcondition reads them directly — no `old`:

<!-- doclint:case p90-swap/final-params-swap-locals-readme-form -->
```groovy
@Ensures({ result.a == b && result.b == a })
static Map<String, Integer> swap(final int a, final int b) {
    int x = a; int y = b
    (x, y) = [y, x]            // parallel multiple assignment — RHS snapshotted before either write
    [a: x, b: y]
}
```

The `final` isn't decoration: it's what *forces* the copy into `x`/`y` and pins the parameters as immutable
inputs, so `b` and `a` in the postcondition are unambiguously their entry values.

Some might regard mutating parameters as poor coding style,
but the verifier ignores such concerns.
If we swap the **parameters themselves**,
then by the time the postcondition runs `a` and `b` no longer hold their
entry values — so you must reach back for them with `old`:

<!-- doclint:case p90-swap/swap-params-result-a-old-b-groovy-12078 -->
```groovy
@Ensures({ result.a == old.b && result.b == old.a })
static Map<String, Integer> swap(int a, int b) {
    (a, b) = [b, a]
    [a: a, b: b]
}
```

That's the rule in miniature: `old` relates the post-state to the *pre-state of something you mutated*; if
you don't mutate it, you don't need it. The `(a, b) = [b, a]` is itself a swap — parallel multiple assignment,
which snapshots the right-hand side before writing any target, so a *sequential* `a = b; b = a` (which would
lose `a`) is provably different and refutes if you claim its outcome. Referring to `old` of a **parameter** —
not just a field — became an *executable* contract in GROOVY-12078; the verifier already modelled it through
its entry-snapshot machinery, so now the proof and the runtime check agree. A wrong relation (`result.a ==
old.a`) refutes either way.

**Lists — mutation under a sound `@Modifies`, with count preservation faithful to Groovy's runtime.**
A `List<Integer>` is the indexed sibling of the Set: contents under array theory + a size oracle
that threads through every size-changing call. `xs.add(v)` stores at the new last index and
grows the size by one; `xs.removeLast()` / `xs.pop()` shrink (refuted on empty via a synth'd
bounds-check obligation); `xs.clear()` zeros the size and every tracked count. The bounded
`bcount(arr, v, 0, size)` matches Groovy's GDK `xs.count(v)` faithfully across all three, so a
stack-shaped push-then-pop *provably* preserves the count:

<!-- doclint:case p40-list-mutation/readme-stack-roundtrip-preserves-count -->
```groovy
class Stack {
    List<Integer> xs
    @Requires({ xs != null })
    @Modifies({ this.xs })
    @Ensures({ xs.count(v) == old.xs.count(v) })       // count preserved across a push-pop round-trip
    void roundTrip(int v) { xs.add(v); xs.removeLast() }
}
```

Drop the `xs.removeLast()` and the postcondition refutes (the add raised the count by one and
there's no compensating pop). Drop the `@Requires({ xs != null })` and the implicit NPE check
on the `xs.add(v)` receiver refutes with a concrete `roundTrip(0)` repro. The Java-style method
idioms `xs.get(i)` / `xs.first()` / `xs.last()` / `xs.set(i, v)` ride the same machinery — the
bounds check on `xs.first()`/`xs.last()`/`xs.removeLast()` is synthesised so pop-on-empty refutes
the same way on an instance field as it does on a parameter. Only the shift-based variants
(`xs.add(i, v)`, `xs.remove(i)`) still defer — their quantified shift modelling stays out of
fragment.

### Act 5 — All the way to a real algorithm

*The capstones the earlier pieces were building toward — nested loops and a matrix sum, a recursive insertion sort proven sorted ∧ permutation, and a fully verified DFS assembled from sets, cardinality, and induction.*

**Nested loops — `count = n·n`, scaling to a flat matrix sum.** A loop may sit inside another loop, each
carrying its own `@Invariant`/`@Decreases`. The textbook case accumulates `n·n` by counting `1` across an
`n × n` grid:

<!-- doclint:case readme-examples/nested-loop-count-n-n -->
```groovy
@Requires({ n >= 0 })
@Ensures({ result == n * n })
static int squareCount(int n) {
    int count = 0, i = 0
    @Invariant({ 0 <= i && i <= n && count == i * n })
    @Decreases({ n - i })
    while (i < n) {
        int j = 0
        @Invariant({ 0 <= j && j <= n && count == i * n + j })
        @Decreases({ n - j })
        while (j < n) {
            count += 1
            j += 1
        }
        i += 1
    }
    count
}
```

The proof **composes**. The outer loop treats the inner loop as a *summarised* cut — havoc what it
writes, then assume `inner_inv ∧ ¬inner_guard`, so on exit `count == i·n + n == (i + 1)·n`, exactly what
the outer invariant needs after `i += 1`. The inner loop's own establishment / preservation / progress are
discharged separately. The subtle, load-bearing point: the inner invariant `count == i·n + j` is
*self-contained* — checked under `inner_inv ∧ inner_guard`, **not** under the outer `count == i·n`, which
is *false while the inner loop runs* (`count` is mid-increment). And a too-weak inner invariant can't slip
a wrong result past the outer check: delete the `count == i·n + j` clause and the outer preservation
fails, because the summary leaves `count` unconstrained (its counterexample shows a free `count$havoc`).

And it scales from scalar accumulators to **arrays**. Summing a flat *n×m* matrix composes three of the
machinery's pieces at once — two nested loops, the array-range `.sum()` aggregation carried as a loop
invariant, and the **nonlinear bound** on the flat read index `a[k]` where `k == i·m + j`:

<!-- doclint:ignore README illustration: matrix sum (nested loop) -->
```groovy
@Requires({ n >= 0 && m >= 0 && a != null && a.length >= n * m })
@Ensures({ result == a[0..<n * m].sum() })
static int matrixSum(int n, int m, int[] a) {
    int sum = 0, i = 0, k = 0
    @Invariant({ 0 <= i && i <= n && k == i * m && sum == a[0..<k].sum() })
    @Decreases({ n - i })
    while (i < n) {
        int j = 0
        @Invariant({ 0 <= i && i < n && 0 <= j && j <= m && k == i * m + j && sum == a[0..<k].sum() })
        @Decreases({ m - j })
        while (j < m) { sum += a[k]; k += 1; j += 1 }
        i += 1
    }
    sum
}
```

The running `sum == a[0..<k].sum()` extends one element per inner step (the `sum$` base/step axioms), the
inner loop is summarised as a cut for the outer, and the `a[k]` read needs `k == i·m + j < n·m ≤ a.length` —
which Z3's nonlinear solver won't derive alone, so the verifier supplies the monotonicity lemma `(i < n ∧ 0 ≤
m) ⟹ i·m + m ≤ n·m` as a sound ground fact (a flat `a[i*m + j] = 0` matrix *fill* verifies the same way).
Out of fragment, all skipping loudly: a third level of nesting, an inner loop with no `@Invariant`, or one
that grows a collection (`xs.add`).

**Putting it all together — a fully verified sort.** Everything above composes into one result: a
recursive in-place insertion sort proven **sorted *and* a permutation of its input** — the two halves of
sorting correctness — with no loops; the recursion *is* the proof, and the array is mutated in place under a
sound `@Modifies` frame (across each call the checker *havocs* the array — conservatively forgets everything
it knew about its contents — and re-derives what it needs from the callee's `@Ensures`, so nothing is
assumed unchanged for free).

> **Soundly, under Phase 24.** The recursive call `insert(m-1, a[m], v)` passes the pivot `a[m]` as the new,
> tight bound — so its precondition needs the *transitive* bound `a[it] <= a[m-1]` for all `it`, which Z3
> can't get from *adjacent* sortedness by e-matching (the solver instantiates a quantified fact only when a
> matching term already appears in the formula). A one-line **monotone-bound lemma** (`maxBound`, proved
> by induction: every element of an adjacent-sorted prefix `[0,k]` is `<= a[k]`) supplies it; called before
> the swap, its `@Ensures` threads through the swap to the recursive call (Phase 24's intervening-mutation
> replay). This is the *sound* discharge of a precondition that, before Phase 24, was passing vacuously via a
> recursive-call name-conflation — a worked example of the lemma-as-instantiation-hint pattern.

Two ghost parameters carry the proof, both ordinary ints the runtime ignores: `hi` is an upper
bound on the active elements (the recursion passes the pivot `a[m]` as the new, tight bound — that
tightness is what lets the order argument go through), and `v` is an arbitrary value whose
*occurrence count* must be preserved (`a.count(v) == old.a.count(v)` for all `v` ≡ same multiset ≡
a permutation). The `every`/`count`/`old` are all plain GDK Groovy, so the same contract is checked
at runtime.

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

Both halves are checked, not assumed: a "sort" that zeroed the array fails the permutation clause, and one
that left elements out of order fails the sortedness clause — bounded quantifiers, induction (`@Decreases`),
the multiset `count` law, `old` pre-state, sound `@Modifies` framing, and a monotone-bound lemma, in one
proof.

**Finite sets — membership and a cardinality law.** A `Set<Integer>` is modelled as a *characteristic
array* — a flag per possible element saying in/out — so `x in s` is a read and `s.add(x)` is a write
the verifier can track. `s.size()` carries one rule: adding an element that isn't already present grows
the size by exactly one. That's the building block for proving a loop or recursion that keeps adding to
a set actually terminates — and that it didn't double-count (e.g. a graph traversal over finite nodes):

<!-- doclint:ignore README illustration: set add (member + size) -->
```groovy
class C {
    Set<Integer> s
    @Requires({ x !in s })            // x is new …
    @Modifies({ this.s })
    @Ensures({ x in s &&                // … so after add it is a member …
               s.size() == old.s.size() + 1 })   // … and the size grew by one
    void put(int x) { s.add(x) }
}
```

Drop the `x !in s` precondition and the `+ 1` no longer holds — `x` might already be present — so
the proof fails with a concrete `put(2)`. **Subset** (`s.containsAll(t)`) and **equality**
(`s.equals(t)`) are in the fragment for enum-element sets (finite-conjunction lowering over the
enum's constants) and for Int-element sets under a `Sets.boundedBy(t, n)` context (bounded
universal). **Union and intersection** are in for *inline* uses — `(a + b).contains(x)` lowers
lazily to `x ∈ a ∨ x ∈ b`, `a.intersect(b).contains(x)` to the conjunction, and `containsAll` on a
binop receiver chains through the finite conjunction over the enum domain. Materialised
assignment (`Set<X> u = a + b` as a fresh first-class set) is **also in**: `u` becomes a known set
whose pigeonhole, full-coverage iff, and per-element membership iff relating it to its operands are
all asserted on mint, so subsequent `u.contains` / `u.containsAll` / `u.size()` reasoning composes
with every other set lowering.

**Finite maps — a value array plus a key-set.** A `Map<Integer,Integer>` is modelled as its values
(`m[k]` / `m.get(k)`, an array) together with its key domain (`m.containsKey(k)` / `k in m`, a *set*).
A `m.put(k,v)` does both — stores the value and adds the key — so value reads, the key frame, and the
key-set cardinality law all hold at once; and because the key-set is the Phase-16 set, `m.size()`
drives the same DFS-shaped recursive measure over a map's key domain:

<!-- doclint:ignore README illustration: map put (frames other keys) -->
```groovy
class C {
    Map<Integer,Integer> m
    @Requires({ j != k })
    @Modifies({ this.m })
    @Ensures({ m[k] == v &&                 // the value just put …
               m.containsKey(k) &&          // … the key is now in the domain …
               m[j] == old.m[j] })          // … every other key is untouched
    void put(int k, int v, int j) { m.put(k, v) }
}
```

`m.containsValue(v)` is in the fragment for enum-keyed maps — a finite disjunction over the
enum's key constants, mirroring the subset lowering on the existential side. Int-keyed and
String-keyed maps still skip honestly (no finite key domain to enumerate).

**Reachability — a recursive graph traversal, verified.** Sets, maps, induction, and bounded quantifiers
compose into the property a search algorithm is *for*: a depth-first traversal of a functional graph
(`next` is a `Map<Node,Node>` successor) marking nodes in a `Set<Node>`. Two reachability postconditions
hold at once — **soundness** (`visited` only ever grows, a bounded universal over the node domain) and
**progress** (the node handed in ends up visited, while the traversal budget lasts). The recursive call
*havocs* `visited` and reframes it from the callee's `@Ensures` (sound `@Modifies`), and the self-`@Ensures`
is the inductive hypothesis:

<!-- doclint:case p18-reachability/fuel-dfs-visited-grows-and-node-covered -->
```groovy
class C {
    Map<Integer,Integer> next   // functional graph: successor of node u
    Set<Integer> visited
    int n                       // node domain 0..<n
    @Requires({ 0 <= u && u < n && (0..<n).every { 0 <= next[it] && next[it] < n } })
    @Modifies({ this.visited })
    @Decreases({ fuel })
    @Ensures({ (0..<n).every { (it in old.visited) ==> (it in visited) } &&
               (fuel <= 0 || (u in visited)) })   // grows monotonically, and u gets covered
    void visit(int u, int fuel) {
        if (fuel > 0 && u !in visited) {
            visited.add(u)
            visit(next[u], fuel - 1)
        }
    }
}
```

The same soundness half also goes through under the set-cardinality measure `@Decreases({ n - visited.size() })`
— the DFS-shaped termination from Phase 16. A traversal that *removes* a node breaks monotonic growth and
refutes.

> *The sections that follow build the verified DFS up from its parts — the counting machinery that proves the
> traversal both **terminates** and **visits every reachable node**. This is the deepest material in the
> README (the kind of proof the Dafny/Verus community uses as a benchmark credential); if you'd rather see
> the tool applied to everyday problems, skip ahead to the [HumanEval Examples](#humaneval-examples).*

**The cardinality axiom — `Sets.boundedBy`.** The uninterpreted set size (Phase 16) knows only its per-mutation
deltas — it has no link to *which* elements a set holds. `Sets.boundedBy(s, n)` supplies the **pigeonhole**
relationship for a set whose elements live in a finite domain `[0, n)`: it means exactly `s ⊆ [0, n)`, and
lowers to `s.size() <= n && (s.size() < n || (0..<n).every { it in s })` — a faithful boolean definition over
the cardinality and a bounded membership universal (no trusted axiom). From it the engine *derives* the two
facts cardinality-driven search rests on:

<!-- doclint:ignore README illustration: full-set coverage + hole -->
```groovy
@Requires({ Sets.boundedBy(s, n) && s.size() == n && 0 <= u && u < n })
@Ensures({ u in s })                       // FULL ⇒ MEMBER: a full bounded set covers the whole domain
static int f(Set<Integer> s, int n, int u) { 0 }

@Requires({ Sets.boundedBy(s, n) && 0 <= u && u < n && u !in s })
@Ensures({ s.size() < n })                 // HOLE ⇒ NOT FULL: a missing in-domain node means room remains
static int g(Set<Integer> s, int n, int u) { 0 }
```

Drop `Sets.boundedBy` from either and the claim refutes — without it the (uninterpreted) size says nothing
about membership. The `HOLE ⇒ NOT FULL` fact is exactly what a cardinality-terminating DFS needs at its
coverage branch.

**Two gaps remain** — *completeness* (every reachable node visited) and
*unconditional* `start ∈ visited` (without a fuel budget). Both are closed by what follows: the
bounded-sum cardinality unlocks the latter, and the frontier/stack invariant lands the former.

**Bounded-sum cardinality — `bcount`, earned by induction.** The genuine count of a set's members in a
domain, `bcount(s,k) = Σ_{i<k} (i ∈ s ? 1 : 0)`, is just an ordinary recursive method — and its foundational
properties are proved by the framework's *own* induction (`@Decreases` on `k`, the self-`@Ensures` as the
hypothesis), no built-in axiom:

<!-- doclint:case p20-bcount/bound-lemma-0-bcount-s-k-k -->
```groovy
@Requires({ k >= 0 })
@Ensures({ 0 <= result && result <= k })          // the BOUND — the converse counting `card` lacked
@Decreases({ k })
static int bcount(Set<Integer> s, int k) {
    if (k == 0) return 0
    int rest = bcount(s, k - 1)
    return rest + ((k - 1) in s ? 1 : 0)
}
```

The same shape with `@Requires({ (0..<k).every { it in s } })` proves `result == k` — **full domain ⇒ count
= k**, tying the count to actual membership. Break the recursion (`rest + 2`) and the bound refutes. These are
the converse-counting facts the uninterpreted `card` and the definitional `Sets.boundedBy` couldn't reach.

**The per-add law — `Sets.boundedCount` as a primitive.** The recursive `bcount` *earns* its bound by induction but
is opaque across a method boundary (and can't take `s ∪ {u}` as an argument), so it can't thread a count
*through a mutation*. `Sets.boundedCount(s, k)` is the same bounded count as a **primitive** — carrying its bound
axiom, and, at every set mutation, the bcount analogue of the per-store `count` law (Phase 12):
`Sets.boundedCount(s∪{u}, k) = Sets.boundedCount(s, k) + (0 <= u < k ∧ u ∉ s ? 1 : 0)`. So a fresh in-domain add raises the
count by exactly one:

<!-- doclint:case p21-bcount-law/fresh-in-domain-add-increments-count -->
```groovy
@Requires({ 0 <= u && u < k && u !in s })
@Modifies({ this.s })
@Ensures({ Sets.boundedCount(s, k) == Sets.boundedCount(old.s, k) + 1 })
void put(int u, int k) { s.add(u) }
```

Drop the freshness guard and the `+ 1` refutes; add an element *outside* `[0, k)` and the count is
unchanged (the law's domain guard); `remove` of a present in-domain element decrements it.

**A DFS that proves the node is reached — unconditionally.** The last piece is the **full-characterization**:
`Sets.boundedCount(s, k) == k ⟺ (0..<k).every { it ∈ s }` — a full count over a `k`-slot domain forces every node
in (the converse of Phase 20's *full ⇒ count*). Both directions are theorems of the count, so the encoder
asserts the iff for every `Sets.boundedCount` term. With it, a **cardinality-terminating** DFS proves the node it is
handed ends up visited — *unconditionally*, no fuel bound — the property that was the honest boundary two
phases ago:

<!-- doclint:case p22-full-char/dfs-unconditional-coverage-start-in-visited -->
```groovy
class C {
    Map<Integer,Integer> next         // functional graph
    Set<Integer> visited
    int n
    @Requires({ 0 <= u && u < n && (0..<n).every { 0 <= next[it] && next[it] < n } })
    @Modifies({ this.visited })
    @Decreases({ n - Sets.boundedCount(visited, n) })          // strictly decreases — the per-add law
    @Ensures({ (u in visited) &&
               (0..<n).every { (it in old.visited) ==> (it in visited) } })   // ← UNCONDITIONAL coverage
    void visit(int u) {
        if (u !in visited && Sets.boundedCount(visited, n) < n) {
            visited.add(u)
            visit(next[u])
        }
    }
}
```

Termination is `n - Sets.boundedCount(visited, n)` (the per-add law makes it drop by one on a fresh add); coverage
closes at the "set full" branch, where `Sets.boundedCount(visited, n) == n` forces — via the full-characterization —
every domain node, `u` included. It composes *everything*: sets, the functional-graph map, induction,
caller-side set framing, bounded quantifiers, the per-add law, and the full-characterization.

**Putting it all together — verified DFS, completeness and all.** A single `visit` call above covers
the node it was handed but **not its successors**: claiming `next[u] in visited` refutes for that one
call, because a node visited earlier needn't have had its edge followed *yet* — the frontier
subtlety. *Completeness* (every reachable node is visited) is the closure fixpoint, and it is now
**fully verified**, in two halves:

- **closure ⇒ every reachable node is visited** (Phase 23/25) — the inductive `propagate` over the chain
  `chain(u,d)` (the `d`-step successor), discharged once a recursive contract function carries its defining
  equation (Phase 25);
- **DFS *establishes* closure** (Phase 26) — the frontier/stack invariant. A plain `mark` provably breaks
  closure (the new node's successor isn't visited yet), so the recursion stack is modelled as a `Set` ghost
  (`onStack`, pushed before recursing, popped after) under the invariant *closed-except-on-stack*: every
  visited node is on the stack **or** its successor is visited. `visit` maintains it and restores the stack,
  so a top-level `dfs` (empty stack in, empty stack out) leaves `visited` **closed under `next`** — every
  visited node's successor is visited.

<!-- doclint:ignore README illustration: DFS with on-stack closure invariant -->
```groovy
@Requires({ 0 <= u && u < n && (0..<n).every { 0 <= next[it] && next[it] < n } &&
            (0..<n).every { (it in visited) ==> (it in onStack || next[it] in visited) } &&   // closed-except-on-stack
            (0..<n).every { (it in onStack) ==> (it in visited) } })                            // onStack ⊆ visited
@Modifies({ [this.visited, this.onStack] })
@Decreases({ n - Sets.boundedCount(visited, n) })
@Ensures({ (u in visited) &&
           (0..<n).every { (it in visited) ==> (it in onStack || next[it] in visited) } &&   // invariant kept
           (0..<n).every { (it in onStack) ==> (it in visited) } &&
           (0..<n).every { (it in onStack) == (it in old.onStack) } &&                          // stack restored
           (0..<n).every { (it in old.visited) ==> (it in visited) } })
void visit(int u) {
    if (u !in visited && Sets.boundedCount(visited, n) < n) {
        visited.add(u); onStack.add(u); visit(next[u]); onStack.remove(u)
    }
}
```

A **call-site soundness fix** (Phase 24) was the prerequisite — `verifyCallSite` wasn't replaying intervening
mutations before a callee's precondition, so a naive closure-threading DFS passed spuriously. With all of it,
**every correctness property of DFS** — termination, soundness, unconditional coverage, and completeness — is
machine-checked, over a cyclic graph, by induction (no loops). See the roadmap.

## HumanEval Examples

The examples above are ours — chosen to showcase the fragment. To check the engine against problems
*we didn't pick*, it's also been run over an **external, real-world corpus**: Verus'
[HumanEval suite](https://github.com/secure-foundations/human-eval-verus), the standard benchmark
for auto-active verifiers on LeetCode-shape problems. Its entries are GPT-generated implementations
that Verus checks for implicit overflow only — *no* functional specs. groovy-verify ports a selection
of them faithfully and **adds the spec the original lacks**, turning an overflow-only check into a
correctness proof.

These weren't tailored to the fragment — they're un-cherry-picked control flow (counted loops, early
returns, conditional list/string mutation, NIA bounds), and porting them is what *drove* several of
the later phases (49a/b early-returns, 48 NIA, 46d in-loop path facts). Where the algorithms are
list / map / loop-shaped, the engine matches or exceeds Verus on what it proves.

Read against the five acts above, the corpus re-runs the same machinery on problems we didn't pick —
and roughly in that arc: **Act 1**'s loop invariants and `@Decreases` carry every example below;
**Act 2**'s NIA bound and divide-by-zero obligations land in `is_prime`; the recurrence tasks extend
**Act 1**'s proof-by-induction — `Fib`/`Trib`/`Gcd`/`Lcm` package common recurrences as named helpers
whose axioms come built in, the same inductive-lemma idiom you can hand-write yourself; and the list
filters, return shapes, and string methods close on **Act 3** over un-curated input.

Task 030 — filter a list to its positive elements:

<!-- doclint:case humaneval-port/get-positive-verus-030-result-size-xs-size -->
```groovy
@Requires({ xs != null })
@Ensures({ result.size() <= xs.size() })            // ← the spec the Verus original omits
static List<Integer> getPositive(List<Integer> xs) {
    List<Integer> positive = []
    int i = 0
    @Invariant({ positive != null && 0 <= i && i <= xs.size() && positive.size() <= i })
    @Decreases({ xs.size() - i })
    while (i < xs.size()) {
        int x = xs[i]
        if (x > 0) {
            positive.add(x)
        }
        i = i + 1
    }
    return positive
}
```

This exercises a wide slice of the fragment in one method: an empty-list factory local
(`[]`), a *conditional list mutation* inside a `while` loop, a `@Decreases` measure for
termination, and an `@Ensures` over the *returned list*'s size — the verifier aliases
`result.size()` to the returned local's threaded size oracle so the postcondition resolves
correctly. The Verus port of the same task has none of that — just the implementation.

Task 035 (`max_element`) is the **witnessed extremum** — its spec is *both* universal and existential
at once: the result is `>=` every element **and** is *equal to* one of them (without the second
clause, a "max" that returned `Integer.MAX_VALUE` would pass). The loop invariant carries both as the
running maximum grows:

<!-- doclint:ignore README illustration: max-element witnessed extremum -->
```groovy
@Requires({ a != null && a.length > 0 })
@Ensures({ (0..<a.length).every { a[it] <= result } &&
           (0..<a.length).any  { a[it] == result } })
static int maxElement(int[] a) {
    int m = a[0], i = 1
    @Invariant({ 1 <= i && i <= a.length &&
                 (0..<i).every { a[it] <= m } && (0..<i).any { a[it] == m } })
    @Decreases({ a.length - i })
    while (i < a.length) { if (a[i] > m) m = a[i]; i = i + 1 }
    return m
}
```

The `any` (bounded existential) is the interesting half — the witness is carried through the loop (and
replaced by index `i` whenever a larger element is found), so the postcondition's existential closes on
a ground witness rather than asking Z3 to invent one. `min` is symmetric, and a "max" that returns
`a[0]` correctly refutes (the universal clause fails — a later element can exceed it; the existential
witness alone isn't enough). No new machinery — just `every`/`any` (Phase 9) inside a loop.

Task 057 (`monotonic`) — is a list all-non-decreasing **or** all-non-increasing — takes that one step further
into a **disjunctive ∀∀ spec**: `result == ((∀ pair: l[j] <= l[j+1]) || (∀ pair: l[j] >= l[j+1]))`. The scan
keeps two boolean flags, and each is a bounded *existential* over the prefix — `increasing == (∃ j < i. l[j] <
l[j+1])`, `decreasing` the mirror — carried in the loop invariant; the body's `if (increasing && decreasing)
return false` is the in-body early-exit machinery. What's notable is that this composed with **no engine change**
at all: two existentials (each over an *adjacent-pair* predicate `l[j] < l[j+1]`, not a single element), the
`!(increasing && decreasing)` no-double-witness invariant, a mid-loop return, and a two-clause disjunctive
postcondition — all from features that already existed. Drop the `|| non-increasing` half and it **refutes** (the
body returns true for an all-decreasing list, which the weaker spec rejects), so the proof is non-vacuous.

Task 003 (`below_zero`) — detect whether a running balance ever goes negative — is the
**sum-aggregation** showcase, and the spec is the *full biconditional*: the result is true iff
**some prefix sum is negative**.

<!-- doclint:ignore README illustration: below_zero biconditional -->
```groovy
@Requires({ operations != null })
@Ensures({ result == (0..operations.size()).any { ((int) operations[0..<it].sum(0)) < 0 } })
static boolean belowZero(List<Integer> operations) {
    int s = 0, i = 0
    @Invariant({ 0 <= i && i <= operations.size() &&
                 s == operations[0..<i].sum(0) &&
                 (0..i).every { ((int) operations[0..<it].sum(0)) >= 0 } })   // no prefix negative yet
    @Decreases({ operations.size() - i })
    while (i < operations.size()) {
        s = s + operations[i]
        if (s < 0) return true
        i = i + 1
    }
    return false
}
```

Both directions of the `⟺` are machine-checked: the early `return true` *witnesses* the existential
(`any`), and the invariant "no prefix is negative yet" (`every`) carries the converse to the
`return false` path. The prefix sum `operations[0..<i].sum(0)` is the idiomatic Groovy spelling, on
the Phase-51 `sum` aggregation. Two Groovy-surface accommodations are worth calling out (the *logic*
needs neither): `sum(0)` rather than `sum()` because Groovy's `[].sum()` is `null`, not `0` (the
`sum(0)` form returns `0` for an empty prefix, keeping the contract runtime-safe); and an `(int)`
cast because the *seeded* GDK `sum(initial)` overload is declared to return `Object` by signature — this is
*not* an erased generic (those are restored in contract closures by GROOVY-12071), so the cast genuinely
stays where the unseeded `xs.sum()` and other typed accessors no longer need one.

Task 008 (`sum_product`) — return both the sum and the product of a list — exercises *two*
aggregations at once. Sum is `xs.sum()`; product has no GDK method, so the idiom is the fold
`xs.inject(1) { a, x -> a * x }`, which the verifier recognises as a product (`prod$`, the
multiplicative sibling of `sum$`). Both accumulate in one loop, and — returning them as the **typed
pair** HumanEval uses — each is proven against its *own* aggregate:

<!-- doclint:ignore README illustration: sum/product Tuple2 -->
```groovy
@Requires({ xs != null && xs.size() > 0 })
@Ensures({ result.v1 == xs.sum() && result.v2 == xs.inject(1) { a, x -> a * x } })
static Tuple2<Integer, Integer> sumProduct(List<Integer> xs) {
    int s = xs[0], p = xs[0], i = 1
    @Invariant({ 1 <= i && i <= xs.size() &&
                 s == xs[0..<i].sum() && p == xs[0..<i].inject(1) { a, x -> a * x } })
    @Decreases({ xs.size() - i })
    while (i < xs.size()) { s += xs[i]; p *= xs[i]; i += 1 }
    return Tuple.tuple(s, p)
}
```

The postcondition pins *each* component to its own aggregate — `result.v1` is exactly the sum, `result.v2`
exactly the product — because a `Tuple2` return binds `result` as a fixed-arity product whose named slots
fold (Phase 79).

`Tuple2` is one of several **return shapes** that verify the same way. The positional form returns a list
literal and reads elements by index — and this is exactly where a declared **`int[]`** return type works
too, since the body's literal coerces to the array (or is written explicitly as `new int[]{…}`) and the
binding keys off the return *expression*, not the declared type:

<!-- doclint:case p78-int-return/sum-product-returns-int-sum-product -->
```groovy
@Requires({ xs != null && xs.size() > 0 })
@Ensures({ result[0] == xs.sum() && result[1] == xs.inject(1) { a, x -> a * x } })
static int[] sumProduct(List<Integer> xs) {
    int s = xs[0], p = xs[0], i = 1
    @Invariant({ 1 <= i && i <= xs.size() &&
                 s == xs[0..<i].sum() && p == xs[0..<i].inject(1) { a, x -> a * x } })
    @Decreases({ xs.size() - i })
    while (i < xs.size()) { s += xs[i]; p *= xs[i]; i += 1 }
    [s, p]   // also: new int[]{s, p}
}
```

`result[0]` / `result[1]` / `result.length` fold just like the tuple slots (Phase 78). The third shape, the
most self-documenting, is a **named-tuple map** — `return [sum: s, product: p]` read back as
`@Ensures({ result.sum == xs.sum() && result.product == … })`, Groovy's map-as-named-tuple idiom (Phase 83);
the **SumMax** example in the [Dafny examples](#dafny-examples) below is a worked instance.
Across all three shapes (and tuple/map *parameters*, Phase 80/84), a component accessor keeps its declared
generic type inside the contract closure — `result.sum` is an `Integer`, `result.v1` an `Integer`, a
`List<Double>` element a `Double` — so *arithmetic* and *ordering* on it type-check directly:
`result.sum <= n * result.max` and `result.v1 + result.v2 == 30` need no `(int)` cast, and nested accessors
(`result.v1.v2`) resolve too. (This relies on **GROOVY-12071**, which restored the contract closure's generic
types — without it an accessor erases to `Object`, so arithmetic on it won't compile.)

The duck-typed `sum()` also covers concatenation — `['a','b','c'].sum() == 'abc'` over a `List<String>`
lowers to the same base/step machinery on the `str.++` monoid, so a running concatenation verifies just like
the numeric running total.

Task 039's inner `is_prime` — the canonical NIA-plus-control-flow benchmark — ports
verbatim to the Verus source shape:

<!-- doclint:case humaneval-port/is-prime-verus-039-full-verus-shape-port -->
```groovy
@Requires({ num >= 0 })
static int isPrime(int num) {
    if (num <= 1) return 0
    if (num <= 3) return 1
    if (num % 2 == 0 || num % 3 == 0) return 0
    int i = 5
    @Invariant({ i >= 5 })
    while (i * i <= num) {
        if (num % i == 0 || num % (i + 2) == 0) return 0
        i = i + 6
    }
    return 1
}
```

Three previously-deferred capabilities compose in one method: **prefix early-returns**
(Phase 49a) carry the trivial-input bailouts, the **NIA bound check `i * i <= num`**
(Phase 48) replaces what used to be the Phase 8a opt-out cliff, the **in-body early-return**
(Phase 49b) covers the "found a divisor → not prime" shortcut, and the loop invariant
`i >= 5` discharges the divide-by-zero obligations on `num % i` and `num % (i + 2)`. The
Verus original has no `@Ensures` (Verus checks implicit overflow); we add a sound
`@Requires({ num >= 0 })` to keep the bound check honest.

Task 055 (`fib`) — the n-th Fibonacci number — is the **textbook iterative-equals-recursive proof**, via a
`Fib.of(i)` spec helper (the two-term-recurrence sibling of `xs.sum()`); our `Fib.of` indexing matches
HumanEval's exactly (`Fib.of(10) == 55`, `Fib.of(8) == 21`). The same generation also underpins task 039's
`prime_fib` (the n-th number that is both prime and Fibonacci), whose *outer* search is a **deliberate
non-target** — an unbounded `while true` whose termination depends on the *open* question of whether
infinitely many Fibonacci primes exist, so no `@Decreases` can exist (even Verus leaves task 039 a `TODO`):

<!-- doclint:ignore README illustration: Fibonacci via Fib.of -->
```groovy
@Requires({ n >= 0 })
@Ensures({ result == Fib.of(n) })
static int fibIter(int n) {
    int a = 0, b = 1, i = 0
    @Invariant({ 0 <= i && i <= n && a == Fib.of(i) && b == Fib.of(i + 1) })
    @Decreases({ n - i })
    while (i < n) { int t = a + b; a = b; b = t; i = i + 1 }
    return a
}
```

`Fib.of(i)` lowers to an uninterpreted `fib$` with base/step axioms; the invariant carries the
recurrence `a == fib(i) ∧ b == fib(i+1)`, re-established across `b = a + b` by the step axiom — so the
loop is proven to compute the recursive definition.

Task 063 (`fibfib`) — the **tribonacci** number `fibfib(n) = fibfib(n-1) + fibfib(n-2) + fibfib(n-3)`
(base `0, 0, 1`) — is the three-term sibling, and shows the recurrence machinery extends mechanically. A
`Trib.of(i)` helper lowers to a `trib$` with the analogous base/step axioms, and the iterative version
carries a *three*-wide window in its invariant — `a == Trib.of(i) ∧ b == Trib.of(i+1) ∧ c == Trib.of(i+2)`
— re-established across `c = a + b + c` by the step axiom (`trib(i+3) == trib(i+2)+trib(i+1)+trib(i)`):

<!-- doclint:ignore README illustration: tribonacci via Trib.of -->
```groovy
@Requires({ n >= 0 })
@Ensures({ result == Trib.of(n) })
static int fibfib(int n) {
    int a = 0, b = 0, c = 1, i = 0
    @Invariant({ 0 <= i && i <= n && a == Trib.of(i) &&
                 b == Trib.of(i + 1) && c == Trib.of(i + 2) })
    @Decreases({ n - i })
    while (i < n) { int t = a + b + c; a = b; b = c; c = t; i = i + 1 }
    return a
}
```

Task 046 (`fib4`) — the **tetranacci** number `fib4(n) = fib4(n-1) + … + fib4(n-4)` (base `0, 0, 2, 0`) — is the
four-term sibling, and confirms the recurrence machinery extends *mechanically* one term wider: a `Tetra.of(i)`
helper lowers to a `tetra$` with the analogous base/step axioms, and the iterative version carries a *four*-wide
window — `a == Tetra.of(i) ∧ … ∧ d == Tetra.of(i + 3)` — re-established across `e = a + b + c + d` by the step
axiom (`tetra(i+4) == tetra(i+3)+…+tetra(i)`). `return a` proves `result == Tetra.of(n)`; same shape as 063,
one degree higher.

Task 013 (`greatest_common_divisor`) is the **two-argument** sibling: a `Gcd.of(a, b)` helper lowers to a
`gcd$ : (Int, Int) -> Int` constrained by Euclid's defining axioms — base `∀x. gcd(x, 0) == x` and step
`∀x, y. y ≠ 0 ⟹ gcd(x, y) == gcd(y, x % y)`. The iterative Euclid loop verifies against it: the invariant
`Gcd.of(x, y) == Gcd.of(a, b)` is preserved by `t = x % y; x = y; y = t` because the step axiom (`y ≠ 0`
from the loop guard) e-matches `gcd(x, y) == gcd(y, x % y)`; at exit `y == 0` the base axiom collapses
`gcd(x, 0)` to `x`; and it terminates on the variant `y`, since `x % y ∈ [0, y)` for `x ≥ 0, y > 0`:

<!-- doclint:ignore README illustration: gcd via Gcd.of (Euclid) -->
```groovy
@Requires({ a >= 0 && b >= 0 })
@Ensures({ result == Gcd.of(a, b) })
static int gcd(int a, int b) {
    int x = a, y = b
    @Invariant({ x >= 0 && y >= 0 && Gcd.of(x, y) == Gcd.of(a, b) })
    @Decreases({ y })
    while (y != 0) { int t = x % y; x = y; y = t }
    return x
}
```

One honest caveat shared by all three helpers: they are **prove-friendly but refute-hostile**. E-matching
certifies a *true* spec quickly (UNSAT of the negation), but a *false* one — say `Gcd.of(12, 8) == 5`
(it's 4) — only soft-fails with "could not decide / timeout": finding a SAT model under an
infinitely-instantiable recurrence axiom defeats MBQI (model-based quantifier instantiation — Z3's strategy
for *building* a model when quantifiers are present). The verifier still rejects it (soundness holds — it
is never a false *pass*); it just can't hand back a counterexample the way a bounds or null violation can.

Task 029 (`filter_by_prefix`) — same shape, with `s.startsWith(p)` substituted for the
positivity check — ports with the same `result.size() <= xs.size()` spec and the natural
in-body null guard `if (xs[i] != null && xs[i].startsWith(prefix))`. Phase 46d threads the
short-circuit `&&` and any enclosing in-loop `if` as path facts during obligation discharge,
so the inner deref obligation discharges under the guard the conjunction establishes — just
like a straight-line method's `if (s != null) s.method()` shape. Reverse-style benchmarks
port on the `List<Character>` API today; `String.reverse()` itself now verifies at the *literal*
level — `"abc".reverse() == "cba"`, literal involution and length — via an uninterpreted `reverse$`
with bidirectional literal pinning (Z3 has no `str.reverse` primitive). *Symbolic* algebra
(`s.reverse().reverse() == s` for a variable `s`) stays out, blocked by the same seq-universal refute
hang as case folding.

**The string methods you use every day — now provable, not just asserted.** Because they map to Z3's
built-in theory of strings (rather than being treated as opaque), a contract over them can be *proven*:
predicates (`startsWith` / `endsWith` / `contains` / `isEmpty`), indexing (`length` / `charAt` /
`substring` / `indexOf`), composition (`+` / `concat` / `replace` / regex `matches`), and
conversion (`Integer.toString` / `parseInt`) all route to Z3 seq-theory primitives;
`toUpperCase` / `toLowerCase` / `equalsIgnoreCase` / `replaceAll` / `lastIndexOf` / `reverse` are
shipped as uninterpreted functions with literal pinning and weak axioms where Z3 doesn't
ship a primitive yet; GString interpolation (`"hello $name"`) folds to chained `str.++`.
Literals fold to ground constants, out-of-range indices refute with the standard
`IndexBounds` diagnostic, and **structural cross-string facts** like
`s.startsWith(t) ∧ i < t.length() ⟹ s.charAt(i) == t.charAt(i)` come free from the theory.
Composing several in one method:

<!-- doclint:case p47h-gstring/showcase-idlength-via-startswith-substring -->
```groovy
@Requires({ s?.startsWith("user:") })
@Ensures({ result == s.length() - 5 })
static int idLength(String s) { s.substring(5).length() }
```

That verifies via two theory consequences chained — `startsWith ⟹ length(prefix) <= length(s)`
gives `s.length() >= 5`, and `substring(s, 5, k).length() == k` gives the identity. A second
showcase blending regex, GString interpolation, and the structural concat facts:

<!-- doclint:case p47h-gstring/showcase-greet-via-gstring-regex-concat-facts -->
```groovy
@Requires({ name ==~ /[a-zA-Z]+/ })
@Ensures({ result.startsWith("Hi, ") && result.endsWith(name) })
static String greet(String name) { "Hi, $name" }
```

No separate `name != null` guard is needed: Groovy's `==~` is null-safe — `null ==~ /…/` is `false`, not an
NPE — so the precondition already excludes null, and the verifier carries that through. The body folds to
`mkConcat(mkString("Hi, "), name)`. Z3's seq theory then knows two
free facts: a literal-prefixed concat starts with that literal (`prefixof(a, a ++ b)`),
and the right operand of the concat is its suffix (`suffixof(b, a ++ b)`). The regex
precondition rides along through whatever shape the body assembles.

The two operations Z3 has *no* primitive for — `reverse` and case folding — are uninterpreted
functions pinned at the literal level, and they **compose**:

<!-- doclint:case p47i-reverse/reverse-composes-with-touppercase -->
```groovy
@Ensures({ result == "CBA" })
static String f() { "abc".reverse().toUpperCase() }
```

`reverse` pins `"abc" → "cba"` and `toUpperCase` pins `"cba" → "CBA"`; Z3's congruence closure
chains the two (`reverse("abc") == "cba"`, so `toUpper(reverse("abc")) == toUpper("cba")`). And it's
**order-independent** — `"abc".toUpperCase().reverse()` proves the same `"CBA"`, because whichever
function is brought up second retroactively pins every literal the first one minted (here `"ABC"`
reverse-pins to `"CBA"`). This is *literal* folding — every link is a ground constant. The moment a
symbolic `s` enters the chain (`s.reverse().toUpperCase()`) it soft-fails cleanly, because the
algebraic universals that would carry it were dropped for poisoning the refute direction (next
paragraph).

**Ranges and character arithmetic — index to letter, end to end.** Groovy ranges and `String.next(i)` (Groovy
6 — the last character shifted by `i`) compose with the range-membership operators, so a small index-to-letter
map verifies completely: the precondition's *integer* range, the body's char shift, and the postcondition's
*character* range are all checked.

<!-- doclint:case p100-string-next/user-example-a-next-i-for-i-in-0-25-in-a-z -->
```groovy
@Requires({ i in 0..25 })
@Ensures({ result in 'A'..'Z' })
static String letter(int i) { 'A'.next(i) }
```

`i in 0..25` lowers to the bounds `0 ≤ i ≤ 25`; `'A'.next(i)` is modelled as a single-char string whose code
point is `'A' + i`; and `result in 'A'..'Z'` is the regex class `[A-Z]`, which bridges to that code point in
Z3 — so the chain proves `65 ≤ 65 + i ≤ 90`. Widen the guard to `0..30` and it **refutes** with `i = 26`
(`'A'.next(26) == '['`, just past `'Z'`). A `String` receiver needs no `!= null` guard either: a range can't
contain null, so `s in 'A'..'Z'` infers `s != null` — the same inference `?.` gets.

**Switch expressions — the same map, spelled out and checked exhaustively.** Where the shift above is
arithmetic, a `switch` expression writes the mapping case by case — and the verifier checks it the same way,
lowering the arrow-switch to an `ite`-chain that composes with both range operators:

<!-- doclint:ignore README illustration: switch-expression letters -->
```groovy
@Requires({ i in 1..3 })
@Ensures({ result in 'a'..'c' })
static String letter(int i) {
    switch(i) {
        case 1 -> 'a'
        case 2 -> 'b'
        case 3 -> 'c'
    }
}
```

The body becomes `ite(i==1, 'a', ite(i==2, 'b', ite(i==3, 'c', …)))`, and `i in 1..3` / `result in 'a'..'c'`
ride the same range machinery as before. It's a *genuine* exhaustiveness check, not a happy-path glance: there's
no `default`, so a no-match yields `null` (Groovy's actual behaviour, modelled as an unconstrained value), and
widening the guard to `i in 1..4` **refutes** with `i = 4` — the `4` case is uncovered. (Switch *expressions*
with simple `int`/`String` labels; the statement form stays out of the fragment.)

The remaining honest gaps: `split` (returns an array, structurally invasive) and symbolic
algebra for `toUpperCase` / `reverse` (universal axioms over the seq sort cause Z3 to
hang in the refute direction) remain deferred. The hard NIA corners (general polynomial identities,
square-root / factoring shapes) may time out under Z3's solver — surfaces as "Could not
decide," never silent. Sister task 023 (`strlen`) ports the same way — with the natural
spec `result == xs.size()` added.

## Dafny Examples

The HumanEval ports above are LeetCode-shape problems. To check the engine against the
proofs the **Dafny** community itself uses as credentials, it's also been run over
canonical examples from Dafny's own materials — its
[online tutorial](https://dafny.org/latest/OnlineTutorial/guide) and the
[VSComp 2010 competition suite](https://github.com/dafny-lang/dafny/tree/master/Source/IntegrationTests/TestFiles/LitTests/LitTest/VSComp2010)
(Leino). They're ported *faithfully* — the Groovy adds nothing the fragment can't express —
and none overlaps the examples above: the existing set has a *witnessed-extremum equality*
(`max_element`), a *sum biconditional* (`below_zero`), and *full `sorted ∧ permutation`*
(insertion sort), but nothing that is a search-returning-index, a nonlinear bound between two
aggregates, or sorted binary search. All three verify — including Dafny's single most iconic
example, binary search.

In the five-act framing these sit with **Act 5** — full-algorithm depth rather than single-property
checks — but measured against the proofs the Dafny/Verus community recognises rather than ones we chose.

### SumMax — `sum ≤ N · max` (VSComp 2010, Problem 1)

Compute the sum and the max of an array in one pass, and prove `sum ≤ N · max`. The whole
proof rides on a *nonlinear* loop invariant, `sum ≤ i · max` — the multiplicative sibling of
the additive prefix-sum invariants. The Dafny original:

```dafny
method M(N: int, a: array<int>) returns (sum: int, max: int)
  requires 0 <= N && a.Length == N && (forall k :: 0 <= k && k < N ==> 0 <= a[k])
  ensures sum <= N * max
{
  sum := 0; max := 0;
  var i := 0;
  while (i < N)
    invariant i <= N && sum <= i * max
  {
    if (max < a[i]) { max := a[i]; }
    sum := sum + a[i];
    i := i + 1;
  }
}
```

Dafny's `returns (sum, max)` is a **named** tuple, so the faithful Groovy is the map-as-named-tuple
idiom (Phase 83): a map literal whose entries the contract references by name, reading exactly like
Dafny's `sum` / `max`. The literal is the method's trailing expression — Groovy returns it implicitly,
which also mirrors Dafny's named out-parameters (there is no explicit `return` of them either):

<!-- doclint:case dafny-port/summax-vscomp10-p1-sum-n-max -->
```groovy
@Requires({ 0 <= n && a.length == n && (0..<n).every { a[it] >= 0 } })
@Ensures({ result.sum <= n * result.max })
static Map<String, Integer> sumMax(int[] a, int n) {
    int sum = 0, max = 0, i = 0
    @Invariant({ 0 <= i && i <= n && sum <= i * max })
    @Decreases({ n - i })
    while (i < n) {
        if (max < a[i]) max = a[i]
        sum += a[i]
        i++
    }
    [sum: sum, max: max]
}
```

The body leans on Groovy's shorthand where it stays unambiguous — compound assignment (`sum += a[i]`,
`i++`) and the implicit trailing-expression return — rather than Dafny's longhand (`sum := sum + a[i];
i := i + 1`). The control structure, the invariant, and the four loop obligations are identical either
way; the shorthand is just less to read.

Preservation is genuine NIA (Phase 48): `sum + a[i] ≤ (i + 1) · max′` needs `i · max ≤ i · max′`
(monotone because `i ≥ 0` and `max ≤ max′`) *and* `a[i] ≤ max′`. The bound is a different
shape from any of our other examples — an *inequality relating two running aggregates*, not an
equality to one — and a deliberately wrong bound (`≤ (N − 1) · max`) refutes with
`fails on: sumMax(new int[0], 0)`. With the return type declared `Map<String, Integer>`, the map values read
back as `Integer` inside the contract closure (GROOVY-12071), so the arithmetic `n * max` and the `<=`
type-check with no `(int)` cast — the postcondition reads exactly as written. The names still earn their keep:
`result.sum` / `result.max` say what they are where positional `result.v1` / `result.v2` (the typed-`Tuple2`
alternative) wouldn't. (Per Leino's own note, the
`a[k] >= 0` precondition isn't actually needed for the postcondition — it's kept here only to stay
faithful to the source.)

### Find — linear search, "not present ⟹ ∀ `a[k] ≠ key`"

The Dafny tutorial's linear search returns an index, or `−1` with a *universal* witness that the
key is absent:

```dafny
method Find(a: array<int>, key: int) returns (index: int)
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
  index := 0;
  while index < a.Length
    invariant 0 <= index <= a.Length
    invariant forall k :: 0 <= k < index ==> a[k] != key
  {
    if a[index] == key { return; }
    index := index + 1;
  }
  index := -1;
}
```

The port reads almost identically:

<!-- doclint:case dafny-port/find-linear-search-index-0-no-element-equals-key -->
```groovy
@Ensures({ result >= 0 ==> result < a.length && a[result] == key })
@Ensures({ result < 0 ==> (0..<a.length).every { a[it] != key } })
static int find(int[] a, int key) {
    int i = 0
    @Invariant({ 0 <= i && i <= a.length && (0..<i).every { a[it] != key } })
    @Decreases({ a.length - i })
    while (i < a.length) {
        if (a[i] == key) return i
        i = i + 1
    }
    return -1
}
```

This is worth pairing with binary search because it is binary search's postcondition *with
sortedness removed* — so it isolates exactly what binary search adds. The in-body early `return i`
(Phase 49b) *witnesses* the found case (binds `result = i` with `a[i] == key`); the invariant
carries the "no earlier element matched" universal to the `return −1` path; and preservation
extends `(0..<i)` to `(0..<i + 1)` in a single quantifier instantiation, because the loop just
checked `a[i] != key` — no transitivity required. A spec claiming the found index holds a
*different* key (`a[result] != key`) correctly refutes.

### BinarySearch — the iconic example

Dafny's flagship tutorial proof, with the `sorted` predicate stated as a *two-dimensional*
quantifier:

```dafny
predicate sorted(a: array<int>)
  reads a
{ forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k] }

method BinarySearch(a: array<int>, value: int) returns (index: int)
  requires 0 <= a.Length && sorted(a)
  ensures 0 <= index ==> index < a.Length && a[index] == value
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
{
  var low, high := 0, a.Length;
  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant forall i :: 0 <= i < a.Length && !(low <= i < high) ==> a[i] != value
  {
    var mid := (low + high) / 2;
    if a[mid] < value { low := mid + 1; }
    else if value < a[mid] { high := mid; }
    else { return mid; }
  }
  return -1;
}
```

The port is the **verbatim** shape — `else return mid` inside the loop, `return -1` after — and it
verifies: both postcondition directions, the excluded-region universal preserved across the narrowing,
every `a[mid]` bound, and termination:

<!-- doclint:case dafny-port/binarysearch-textbook-return-mid-both-directions-bounds-termination -->
```groovy
@Requires({ a.isSorted() })
@Ensures({ result < 0  ==> (0..<a.length).every { a[it] != value } })
@Ensures({ result >= 0 ==> result < a.length && a[result] == value })
static int binarySearch(int[] a, int value) {
    int low = 0, high = a.length
    @Invariant({ 0 <= low && low <= high && high <= a.length &&
                 (0..<low).every { a[it] != value } && (high..<a.length).every { a[it] != value } })
    @Decreases({ high - low })
    while (low < high) {
        int mid = low + (high - low).intdiv(2)
        if (a[mid] < value) low = mid + 1
        else if (value < a[mid]) high = mid
        else return mid
    }
    return -1
}
```

The one authoring subtlety worth calling out — and it's a *spec* choice, not an engine detail — is **how
sortedness is stated**. The natural one-dimensional spelling, the adjacent form
`(1..<a.length).every { a[it - 1] <= a[it] }`, doesn't carry the proof: narrowing `low = mid + 1` needs
`a[i] ≤ a[mid]` for *all* `i ≤ mid`, which is range transitivity — induction, not a single instantiation.
The contract above instead writes it the **native** way, `a.isSorted()` — Groovy 6's GDK predicate
(ascending, ties allowed; the primitive `int[]` and `long[]` overloads are native, and the boolean-getter
property `a.sorted` works too) — which the engine lowers to the *two-dimensional* axiom
`∀ j,k. 0 ≤ j < k < n ⟹ a[j] ≤ a[k]` with an explicit multi-pattern trigger `{a[j], a[k]}`, so the gap
fact `a[i] ≤ a[mid]` fires in a single deterministic instantiation. The explicit `Sorted.ascending(a)` /
`.descending` / `.strictlyAscending` helpers (`verification.Sorted`, a sibling of `Forall`/`Sets`) are the
same thing for the orderings without a native spelling. Either way it's all the spec needs; without it,
preservation refutes on a concrete *unsorted* counterexample (`[7719, 7718]`) — the proof genuinely rests
on sortedness. Dafny's verbatim binary search then verifies, structure-for-structure.

## OpenJML Examples

[OpenJML](https://www.openjml.org/) is the JML verifier for Java — the closest existing tool to
this one on the JVM, and named as prior art above. Its [examples page](https://www.openjml.org/examples/)
collects small, self-contained proofs chosen to each show *one* idea. Two of them have been ported here.
Examples ported from openjml.org are © their authors, used under the page's **CC BY-NC** terms.

The first is already above, in **Act 3**: the [BitVectors tutorial](https://www.openjml.org/tutorial/BitVectors)
— round a number up to the next multiple of a power of two with `(n + 0xF) & ~0xF`, proven against the
arithmetic spec it's meant to implement, counterexample at `Integer.MIN_VALUE` and all. The second is here.

### Max by elimination — a disjunctive loop invariant

Find the index of a maximum element, but not by the usual running-best scan. Instead, hold a window
`[x, y]` over the array and shrink it from whichever end is no larger, until it collapses to a single
index. The OpenJML original (`MaxByElimination`) is a worked example of an invariant that most first
attempts get *wrong*:

```java
//@ requires a.length > 0;
//@ ensures 0 <= \result && \result < a.length;
//@ ensures (\forall int i; 0 <= i && i < a.length; a[i] <= a[\result]);
int max(int[] a) {
    int x = 0, y = a.length - 1;
    //@ maintaining 0 <= x && x <= y && y < a.length;
    //@ maintaining (\forall int i; 0<=i && i<x; a[i] <= a[y]) && (\forall int i; y<i && i<a.length; a[i] <= a[y])
    //@            || (\forall int i; 0<=i && i<x; a[i] <= a[x]) && (\forall int i; y<i && i<a.length; a[i] <= a[x]);
    //@ decreasing y - x;
    while (x != y) { if (a[x] <= a[y]) x++; else y--; }
    return x;
}
```

The Groovy is the same proof, structure for structure:

<!-- doclint:case p104-openjml/max-by-elimination-result-indexes-a-maximum -->
```groovy
@Requires({ a != null && a.length > 0 })
@Ensures({ 0 <= result && result < a.length && Forall.range(0, a.length) { int i -> a[i] <= a[result] } })
static int max(int[] a) {
    int x = 0
    int y = a.length - 1
    @Invariant({ 0 <= x && x <= y && y < a.length &&
        ((Forall.range(0, x) { int i -> a[i] <= a[y] } && Forall.range(y + 1, a.length) { int i -> a[i] <= a[y] }) ||
         (Forall.range(0, x) { int i -> a[i] <= a[x] } && Forall.range(y + 1, a.length) { int i -> a[i] <= a[x] })) })
    @Decreases({ y - x })
    while (x != y) { if (a[x] <= a[y]) x = x + 1 else y = y - 1 }
    return x
}
```

The lesson the example exists to teach is the shape of that invariant. It is **disjunctive**: at every
step the maximum-so-far sits at *one* of the two endpoints — but which one isn't fixed, it flips each time
the window shrinks from the other side. A single-disjunct invariant (`everything ≤ a[x]`) isn't preserved
when you advance `x`; you genuinely need the *or*. The engine carries the disjunction through preservation
and then, at loop exit where `x == y`, collapses both arms onto the same index to discharge the
postcondition `∀i. a[i] ≤ a[result]`. `@Decreases({ y - x })` proves termination. Flip the postcondition to
claim `result` indexes a *minimum* and it refutes — the proof rests on the maximum direction of the
invariant, not on the loop merely running.

### ChangeCase — the same proof, on the array theory

OpenJML's `ChangeCase` upper-cases a buffer character by character. The natural Groovy — build a `String` by
concatenation in a loop — is the one shape Z3's string theory *can't* carry: a content invariant over `str.++`
(`∀i. r.charAt(i) == …`) times out, because re-establishing a quantified fact across each concat is a
quantifier-on-quantifier induction its seq solver won't close (measured: stuck even with a hand-supplied
`nth`-of-concat lemma and a 30s budget). The *same* content invariant over an **array** discharges at once —
Z3's array theory is exactly where the engine's quantified-loop machinery already lives (it's how **Act 5**'s
matrix fill proves `∀. a[it] == 0`). So spell the buffer as a `char[]` (an Int-element array — `char` is
integral) and ChangeCase falls straight out, with no new engine support beyond folding the char literal:

<!-- doclint:case p106-char-seq/functional-changecase-upper-verifies -->
```groovy
@Requires({ a != null })
@Ensures({ result.length == a.length &&
    (0..<a.length).every { result[it] == ((a[it] >= ('a' as char) && a[it] <= ('z' as char)) ? (char)((int) a[it] - 32) : a[it]) } })
static char[] upper(char[] a) {
    char[] r = new char[a.length]
    int i = 0
    @Invariant({ 0 <= i && i <= a.length && r.length == a.length &&
        (0..<i).every { r[it] == ((a[it] >= ('a' as char) && a[it] <= ('z' as char)) ? (char)((int) a[it] - 32) : a[it]) } })
    @Decreases({ a.length - i })
    while (i < a.length) {
        if (a[i] >= ('a' as char) && a[i] <= ('z' as char)) r[i] = (char)((int) a[i] - 32)
        else r[i] = a[i]
        i = i + 1
    }
    return r
}
```

The whole element-wise postcondition proves — `result` *is* the upper-cased copy, not merely "has no lowercase
left" — and dropping the lowercase guard from the spec refutes. Two Groovy spelling notes: `('a' as char)` is
the char literal (no primitive char syntax exists, and `char >= String` doesn't type-check), and the
arithmetic is `(char)((int) a[i] - 32)` because `char[]` subscripts box to `Number`. The seq-vs-array split is
the real lesson — *the same proof, opposite tractability, decided by which theory you hand Z3.*

## Concurrency "lite" Examples

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

Those two disclaimed halves are exercised on this exact example by the runtime checkers in [`docs/`](docs/): a
**Lincheck** spike (`./gradlew concurrentTest`) shows a `synchronized` `Account` is linearizable while an
unlocked one races, and a **Fray** spike (`./gradlew frayCheck`) drives the JVM scheduler over a two-account
bank transfer to confirm ordered locking is deadlock-free — and to catch the lock-ordering deadlock when it
isn't. Same boundary, made concrete; see [`docs/README.md`](docs/README.md).

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
the [information-flow examples](#information-flow--taint-tracking-generalized) further down: the buffer element's
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
> Lincheck spike in [`docs/`](docs/) exercises it on the real bytecode. Three rungs, three jobs: this checker
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

**The other half — the structural guarantee — lives in [`docs/`](docs/).** That is the part this checker
*assumes*, made runnable on this exact buffer by two complementary tools: a **TLA+** model (`docs/Buffer.tla`)
that TLC explores across *every* interleaving — where the rely stops being an assumption and becomes a checked
theorem about the peer's action, and liveness is checkable too — and a **Lincheck** test
(`src/concurrent/`) that model-checks the *real bytecode* of a lock-free `SpscBuffer`, catching the same leak as
a linearizability violation. Three rungs — compile-time proof here, exhaustive model, tested bytecode — each
trading coverage for fidelity; see [`docs/README.md`](docs/README.md). Run them with `./gradlew tlcCheck` and
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

## Other Examples

A few more that don't belong to one of the per-source sections above: a verified mutable data structure, a
fully-verified classic challenge from the verification-competition literature (ported faithfully and credited to
its source), a Dafny-style element-wise array-fill (FizzBuzz), an algebraic law over arbitrary strings (concat
is associative but not commutative), and a tour of verification across a Groovy type hierarchy — inheritance,
behavioral subtyping, and traits.

### Bean Validation constraints — preconditions you already wrote

A `jakarta.validation` (or legacy `javax.validation`) numeric constraint on a parameter is read as a method-entry
**precondition** — the same posture as `@Requires`: assumed in the body, the caller's obligation. So an annotation
you wrote for *runtime* validation also discharges a *compile-time* obligation, for free:

<!-- doclint:case jakarta-validation/positive-divisor-verifies -->
```groovy
class C { static int f(@Positive int x) { 100 % x } }
```

The `jakarta.validation.constraints.@Positive` gives `x > 0`, so the modulus divisor is non-zero and the implicit
divide-by-zero obligation discharges. Drop the `@Positive` and the same body refutes with `fails on: f(0)`. The
engine matches these by fully-qualified name — it carries no dependency on the validation API — and maps
`@Positive` / `@PositiveOrZero` / `@Negative` / `@NegativeOrZero` / `@Min(n)` / `@Max(n)` to the obvious bound on an
`int` / `long`, and `@Size(min, max)` / `@NotEmpty` to the size of an array, `List`, or `String` (so a
`@NotEmpty int[] a` discharges `a[0]`). `@NotNull` is already read by the null layer. Contradictory constraints
(`@Positive @Negative`) are flagged as a vacuous precondition, not silently passed — and under `VERIFY_EXPLAIN` a
proof that leaned on one prints `also leaned on: @Positive x`.

### Ring buffer — a verified mutable data structure

[Toccata/Why3's `ring_buffer`](https://toccata.gitlabpages.inria.fr/toccata/gallery/ring_buffer.en.html) (after
Leino's Dafny tutorial) is a bounded queue backed by an array. It's the first example here whose subject is
**object state that changes**: a class with mutable fields and a *type invariant* every method must preserve.

<!-- doclint:ignore README illustration: bounded Queue enqueue/dequeue -->
```groovy
@Invariant({ 0 < data.length && 0 <= m && m <= n && n <= data.length })
class Queue {
    int[] data
    int m
    int n

    @Requires({ n < data.length })
    @Ensures({ n == old.n + 1 && data[old.n] == x && (0..<old.n).every { data[it] == old.data[it] } })
    void enqueue(int x) {
        data[n] = x
        n = n + 1
    }

    @Requires({ m < n })
    @Ensures({ result == old.data[old.m] && m == old.m + 1 })
    int dequeue() {
        int r = data[m]
        m = m + 1
        return r
    }

    @Ensures({ result >= 0 })
    int size() { return n - m }
}
```

The class `@Invariant` *is* the contract: the engine **assumes it on entry** and **checks it preserved on
exit** of every method. So `size()` proves `>= 0` only because `m <= n` is assumed; `enqueue` proves it wrote
the tail and left the rest alone (`(0..<old.n).every { data[it] == old.data[it] }`, the array-region frame via
`old.data[it]`) while keeping `n <= data.length`; and an unguarded mutator that breaks the invariant refutes
with *"Cannot prove class invariant"*. We drop Why3's ghost `seq contents` — the engine has no model fields —
and specify directly over the live region `data[m..n)`. This is the non-wrapping bounded version (no modulo),
matching the source.

### Duplets — two duplicate pairs, fully verified (FoVeOOS'11 Challenge 3)

[The challenge](https://toccata.gitlabpages.inria.fr/toccata/gallery/Duplets.en.html): in an array with at
least two repeated values, return two *distinct-valued* duplicate pairs. It's the engine's most-composed
proof — a **witness search proven total**, then **called twice across methods**. Build it in three steps.

First, `duplet`: scan all pairs, return the first duplicate. The hard part is **totality** — given a duplicate
*exists*, prove a real one is *returned*, not the sentinel:

<!-- doclint:case p111-duplets-totality/duplet-totality-verifies -->
```groovy
@Requires({ a != null && (0..<a.length).any { int p -> (p + 1..<a.length).any { int q -> a[p] == a[q] } } })
@Ensures({ 0 <= result.v1 && result.v1 < result.v2 && result.v2 < a.length && a[result.v1] == a[result.v2] })
static Tuple2<Integer, Integer> duplet(int[] a) {
    int i = 0
    @Invariant({ 0 <= i && i <= a.length &&
        (0..<i).every { int p -> (p + 1..<a.length).every { int q -> a[p] != a[q] } } })
    @Decreases({ a.length - i })
    while (i < a.length) {
        int j = i + 1
        @Invariant({ 0 <= i && i < a.length && i + 1 <= j && j <= a.length &&
            (0..<i).every { int p -> (p + 1..<a.length).every { int q -> a[p] != a[q] } } &&
            (i + 1..<j).every { int q -> a[i] != a[q] } })
        @Decreases({ a.length - j })
        while (j < a.length) {
            if (a[i] == a[j]) return Tuple.tuple(i, j)
            j = j + 1
        }
        i = i + 1
    }
    return Tuple.tuple(-1, -1)
}
```

The load-bearing invariant is the nested **∀∀ "no duplicate found yet"** — `∀p<i. ∀q>p. a[p] ≠ a[q]`. At loop
exit `i == a.length` it says *no duplicate anywhere*, contradicting the existential precondition (Z3
instantiates the universal at the existential's witness), so the sentinel path is unreachable. Drop the
existential and it refutes — the proof genuinely rests on it.

Then `dupletExcept(a, except)` is the same search with one extra conjunct, `a[i] != except` — find a duplicate
whose *value* differs from `except`. And `duplets` composes the two across method calls:

<!-- doclint:case p113-interproc-tuple/full-two-pass-duplets-composition -->
```groovy
@Requires({ a != null && (0..<a.length).any { int i -> (i + 1..<a.length).any { int j ->
    (0..<a.length).any { int k -> (k + 1..<a.length).any { int l ->
        a[i] == a[j] && a[k] == a[l] && a[i] != a[k] } } } } })
@Ensures({ 0 <= result.v1 && result.v1 < result.v2 && result.v2 < a.length && a[result.v1] == a[result.v2] &&
           0 <= result.v3 && result.v3 < result.v4 && result.v4 < a.length && a[result.v3] == a[result.v4] &&
           a[result.v1] != a[result.v3] })
static Tuple4<Integer, Integer, Integer, Integer> duplets(int[] a) {
    Tuple2<Integer, Integer> r1 = duplet(a)
    Tuple2<Integer, Integer> r2 = dupletExcept(a, a[r1.v1])
    return Tuple.tuple(r1.v1, r1.v2, r2.v1, r2.v2)
}
```

Each call's `@Ensures` constrains the returned tuple's slots; the second call's precondition — *a duplicate
with value ≠ the first exists* — follows from the two-distinct-duplets precondition (since `a[i] ≠ a[k]`, one
of the two known duplicates differs from `a[r1.v1]`). The result: two pairs with provably different values.
Nothing here is a special case — the nested witness search, the tuple returns, and binding a local to a
tuple-returning call are all general capabilities; Duplets just needs all three at once.

### FizzBuzz — element-wise array correctness

A small array-fill in the style Dafny tutorials use to teach element-wise verification — a pure specification
`spec(n)`, a loop that fills `r[i] = spec(i + 1)`, and a postcondition saying **every** slot matches it.
FizzBuzz conventionally counts from 1 (`1, 2, Fizz, …`), so the 0-based array slot `i` holds the value for
number `i + 1` — that `+ 1` is the bridge between the array index and the FizzBuzz number, and it's exactly what
the broken variant below gets wrong. The emoji-FizzBuzz flourish is borrowed, with thanks, from Don Raab's
[*Ternary, Predicate, and Pattern Matching for FizzBuzz with Java 26*](https://donraab.medium.com/ternary-predicate-and-pattern-matching-for-fizzbuzz-with-java-26-646c812a137b).

<!-- doclint:case p-fizzbuzz/fizzbuzz-array-fill-with-number-default-n-tostring -->
```groovy
class FizzBuzz {
    @SelfEnsures   // the body *is* the spec — lifted into @Ensures({ result == <body> }), written once
    static String spec(int n) { n % 15 == 0 ? '🥤🐝' : (n % 3 == 0 ? '🥤' : (n % 5 == 0 ? '🐝' : n.toString())) }

    @Requires({ upTo >= 1 })
    @Ensures({ result.length == upTo })                                           // exactly the size requested
    @Ensures({ (0..<upTo).every { int k -> result[k] == FizzBuzz.spec(k + 1) } }) // every element provably correct
    static String[] build(int upTo) {
        String[] r = new String[upTo]
        int i = 0
        @Invariant({ 0 <= i && i <= upTo && r.length == upTo && (0..<i).every { int k -> r[k] == FizzBuzz.spec(k + 1) } })
        @Decreases({ upTo - i })
        while (i < upTo) { r[i] = FizzBuzz.spec(i + 1); i = i + 1 }
        return r
    }
}
// build(20) == [1, 2, 🥤, 4, 🐝, 🥤, 7, 8, 🥤, 🐝, 11, 🥤, 13, 14, 🥤🐝, 16, 17, 🥤, 19, 🐝]
```

The proof shows:
* the array is the right length
* the loop terminates
* **no slot can hold the wrong value** — `spec` is self-specifying (`@SelfEnsures` lifts its body into
  `@Ensures({ result == <body> })`), so the body's `spec(i + 1)` and the invariant's `spec(k + 1)` are one term
  and the every-quantifier extends by one element per step

Break it and it refutes, naming the offending slot. Write `r[i] = spec(i)` instead of `spec(i + 1)` and the loop
invariant isn't preserved; the diagnostic reports the actual element against the spec:

```
[Static type checking] - Cannot prove loop invariant is preserved by the loop body in build
    invariant: ((((0 <= i) && (i <= upTo)) && (r.length == upTo)) && (0..<i).every({ int k -> ... }))
    counterexample: i = 0, r.length = 1, upTo = 1
    r[0] = "🥤🐝" — the spec requires "1"
    fails on: build(1)
```

Slot 0 holds `spec(0) == "🥤🐝"` (0 divides everything, so it's FizzBuzz) where it must hold `spec(1) == "1"`.
"Correct" here means *faithful to `spec`*: the loop provably realizes it at every index, with no gap, overwrite,
or off-by-one. It doesn't argue the spec itself is the One True FizzBuzz.

### String concatenation — an algebraic law, proved and disproved

The FizzBuzz example reasons about strings *element by element*; this one reasons about them *algebraically*.
Groovy's `+` on `String` lowers to the SMT theory of sequences, where concatenation is **associative but not
commutative** — and the verifier proves the law that holds for every string while refuting the one that doesn't,
over *arbitrary* strings (not concrete literals):

<!-- doclint:ignore README illustration: String concat associative/commutative -->
```groovy
class StringConcat {
    @Ensures({ (a + b) + c == a + (b + c) })           // holds for all a, b, c — proved
    static void associative(String a, String b, String c) { }

    @Ensures({ a + b == b + a })                        // not a law — refuted
    static void commutative(String a, String b) { }
}
```

`associative` verifies. `commutative` cannot — and the diagnostic names a minimal witness rather than just
failing:

```
[Static type checking] - Cannot prove postcondition of commutative holds on this return path
    ensured: ((a + b) == (b + a))
    fails on: commutative("A", "B")
```

That is, `"A" + "B"` = `"AB"` ≠ `"BA"` = `"B" + "A"`. The postcondition is written purely over the parameters,
so the method body can stay empty — the property *is* the specification. (Phrasing it as a `boolean`-returning
method whose body is the comparison, with `@Ensures({ result == true })`, works identically.)

### Inheritance, traits & behavioral subtyping

Verification follows the type hierarchy, not just single classes. Three capabilities, each grounded in a tested
example. (Note: every class needs its own `@TypeChecked` — the extension isn't inherited.)

**Inherited invariants and `super` calls.** A subclass method is proved against the *conjunction* of its own and
every ancestor's class `@Invariant`, and a `super.m(…)` call is treated like any contracted call — the parent's
`@Ensures` is assumed for the result, its `@Requires` discharged at the site — so a child can prove a
strengthened postcondition built on the parent's:

<!-- doclint:ignore README illustration: inheritance super-call postcondition -->
```groovy
class Base    { @Requires({ x >= 0 }) @Ensures({ result == x * 2 })     int f(int x) { x + x } }
class Derived extends Base { @Ensures({ result == x * 2 + 1 }) int g(int x) { super.f(x) + 1 } }  // proven
```

**Behavioral subtyping (the Liskov substitution principle).** This is the engine's one check that relates *two
contracts* rather than a contract to a body. When an override **redeclares** its contract, groovy-verify proves
it stays substitutable for the method it overrides: the precondition must be **weakened**
(`pre_parent ⟹ pre_child` — accept every call the parent did) and the postcondition **strengthened**
(`(pre_parent ∧ post_child) ⟹ post_parent` — promise at least as much). Pure SMT implication checks over the
shared parameter/field/result namespace, with a concrete witness on failure. Take a bank account whose `debit`
may draw down to zero:

<!-- doclint:ignore README illustration: LSP weaken/strengthen precondition -->
```groovy
class Account {
    int balance
    @Requires({ 0 <= amount && amount <= balance })   // may withdraw up to the whole balance
    @Ensures({ result == balance - amount })
    int debit(int amount) { balance - amount }
}

class GoldAccount extends Account {                    // overdraft: accepts MORE — precondition weakened ✓
    @Requires({ 0 <= amount && amount <= balance + 1000 })
    @Ensures({ result == balance - amount })
    int debit(int amount) { balance - amount }         // proven substitutable
}

class RestrictedAccount extends Account {              // min-balance: accepts LESS — precondition strengthened ✗
    @Requires({ 0 <= amount && amount <= balance - 100 })
    @Ensures({ result == balance - amount })
    int debit(int amount) { balance - amount }
}
```

`GoldAccount` verifies — it honours every call `Account` would. `RestrictedAccount` is **refuted**: a caller
holding an `Account` may legitimately `debit` its whole balance, but if the object is really a
`RestrictedAccount` that call is rejected — so it is not a true subtype. The diagnostic names the rule and gives
a witness:

```
Liskov substitution violation in override 'debit': its precondition is not behaviourally compatible with the overridden method
    rule: @Requires must be weakened (or kept), never strengthened, in an override
    counterexample: amount = 0, balance = 0
    fails on: debit(0)
```

(The postcondition direction is symmetric: a child that *weakens* its `@Ensures` — promising less than the
parent — refutes the same way.)

**Interface contracts.** A `@Requires` / `@Ensures` an `interface` method declares is inherited by every
implementing class — so an interface can hand its implementers a precondition. Here `NonZero` promises a non-zero
argument, and that inherited `@Requires` is exactly what discharges the implicit divide-by-zero obligation in
`Calc.half` — drop `implements NonZero` and the same body refutes with `d = 0`:

<!-- doclint:case p123-interface-contracts/interface-requires-guards-the-implementer-body-verifies -->
```groovy
interface NonZero {
    @Requires({ d != 0 })
    int half(int d)
}

@TypeChecked(extensions = 'verification.VerifyChecker')
class Calc implements NonZero {
    int half(int d) { 100.intdiv(d) }
}
```

(The interface itself carries no `@TypeChecked` — its contract closure is stock groovy-contracts; only the
implementing class is verified, against the contract it inherits.)

**Traits.** A trait's class `@Invariant` is enforced across the `implements` axis (the same monitor-invariant
proof, one axis over) — on the trait's *own* default methods **and** every implementing class's methods, which
all reason over the woven trait state. A wrap-around counter — the trait owns the state, a wrapping `inc`, and
the `0..9` invariant; an implementing class adds a wrapping `dec` — proves both methods keep the counter in
range:

<!-- doclint:ignore README illustration: trait wrap-around Counter -->
```groovy
@Invariant({ 0 <= count && count <= 9 })
trait Counter {
    int count
    int getCount() { count }
    void inc() { count = (count == 9 ? 0 : count + 1) }   // trait's own method — proven to wrap, not overflow
}

class WrapCounter implements Counter {
    void dec() { count = (count == 0 ? 9 : count - 1) }   // implementer's method — proven to wrap, not underflow
}
```

Drop the wrap from either `inc` (`count = count + 1`) or `dec` and the invariant refutes at the boundary
(`count == 9` / `count == 0`). The trait's default method is verified by recovering its pre-weave body and
rewriting the woven field accessors back to plain field access, so it rides the same machinery as an ordinary
method. One honest boundary remains on both axes: a method is verified only against the contract it *declares* —
an inherited `@Ensures` isn't re-checked against an *uncontracted* override (groovy-contracts still enforces it
at runtime).

### Inline assertions — a Dafny-style `assert`

A bare Groovy `assert P` in a verified method is discharged at *compile* time, not only at runtime. The trivial
cases behave as you'd hope:

<!-- doclint:ignore README illustration: assert compile / no-compile -->
```groovy
class C {
    static void ok()  { assert 2 < 3 }    // compiles
    static void bad() { assert 3 < 2 }    // does not compile
}
```

```
[Static type checking] - Assertion may not hold: (3 < 2)
```

The substance is `assert P(state)` — proved from the reaching context (`@Requires`, prior assignments, enclosing
guards), and refuted with a concrete counterexample when the context doesn't justify it:

<!-- doclint:ignore README illustration: assert from @Requires -->
```groovy
@Requires({ x > 5 })
static void f(int x) { assert x > 0 }     // verified — x > 5 ⟹ x > 0

static void g(int x) { assert x > 0 }     // refuted — counterexample x = 0
```

A verified `assert` means *prove this holds here*, not *check it at runtime* — so `g`'s assertion over a parameter
the signature doesn't constrain is refuted, and the diagnostic nudges toward the right tool:

```
[Static type checking] - Assertion may not hold: (x > 0)
    counterexample: x = 0
    hint: if this is a caller precondition, declare it as @Requires({ (x > 0) }) — it is then documented and checked at every call site.
```

A *proven* assert is then **used as a fact** downstream — both by the implicit safety checks (`assert i < n; …
a[i]`) and by the method's `@Ensures` — so a proof can be broken into steps the solver reaches one at a time.
That's the bounded core of Dafny's `assert`, kept sound by **assume/enforce**: the assert is *enforced* as its own
obligation, so assuming it is sound, and a false assert is reported rather than silently assumed. Straight-line
code and `if`/`else`; an assert past a re-assignment or inside a loop is loudly skipped rather than checked. (This
also fixed a wart — an `assert` in a body used to make the postcondition walk bail and *silently skip the
`@Ensures`*; it is now carried through, so the contract is still checked.)

A failing `assert` throws `AssertionError`, so a *verified* assert is one more proof that an exception can't escape
here — the same totality guarantee as the bounds/null/division checks. In particular, **`assert false` is the
unreachability idiom**: it *verifies* exactly when the path is contradictory (genuinely dead code, e.g.
`@Requires({ x > 0 })` then `if (x < 0) { assert false }`) and *refutes*, with a counterexample, when the point is
actually reachable.

> **`assert` is not a substitute for a contract.** It's tempting, now that assertions are checked, to write
> `assert x > 0` as a method's first statement instead of `@Requires({ x > 0 })`. Don't — they put the obligation
> in *opposite* places. `@Requires` is **assumed** in the body and **proved at every call site**, so `f(0)` is
> rejected at the *caller* and the body may rely on `x > 0`. An `assert` must be **proved inside the body** (from
> nothing — so it refutes, as `g` does) and constrains **no caller** — the failure lands in the wrong place. The
> split runs through all of them: `@Ensures` names `result` and `old(…)` and is what *callers* assume about the
> return value; `@Invariant` holds across every method; an override is checked for behavioural subtyping against
> the contract it inherits — and the annotations are *declarative specifications* read by groovy-contracts (runtime
> enforcement), by a consumer compiling against your jar, by IDEs, doc tools, and AI agents. An inline `assert`
> does none of that. **Rule of thumb: contracts describe the interface (what callers see and rely on); `assert`
> helps prove the implementation (an internal step the verifier can't take alone).**

### Loop-invariant inference — the common counter loop, no `@Invariant`

Every loop above carries a hand-written `@Invariant`. For the *most common* shape — a counter walking an array —
the engine can infer it. You opt in through the **parameterised extension syntax** — the same mechanism
`NullChecker` uses for `strict`:

<!-- doclint:case pl-infer/counter-loop-over-array-bounds-inferred-no-invariant -->
```groovy
@TypeChecked(extensions = 'verification.VerifyChecker(inferLoops: true)')
class C {
    static int sum(int[] a) {
        int s = 0
        for (int i = 0; i < a.length; i++) { s = s + a[i] }   // array bounds PROVEN — no @Invariant written
        return s
    }
}
```

The engine recognises the `for (int i = lo; i < hi; i++)` counter and synthesises the lower-bound invariant
`lo <= i`; the upper bound `i < a.length` comes straight from the guard, so `a[i]` is proven in bounds. The
inferred bound is **sound by construction** — `lo <= i` holds at entry (`lo <= lo`) and is preserved as the counter
only grows, so inference can never raise a spurious *"invariant not established"* error; it only ever turns a loop
that *had* no invariant into a verified one. It even **removes** a diagnostic: without it, the per-method analysis
can't see `i` is bounded and reports a *possible* out-of-bounds — the inferred `0 <= i` makes that disappear.

This is a deliberately small first slice — a CodeContracts/Clousot-style *"infer cheaply, check with the SMT core"*
idea: C-style `for` counters, the lower bound only, so **safety, not termination** (no variant is inferred — exactly
as a hand-written safety loop verifies with `@Invariant` and no `@Decreases`). It is **opt-in and off by default**:
without `inferLoops: true`, every loop still needs its `@Invariant`, unchanged. `while`-shaped counters, the upper
bound, and an automatic (non-opt-in) mode are the named next steps.

## Information flow — taint tracking, generalized

Compile-time **taint analysis** — Ballerina's `@tainted`/`@untainted`, the OWASP-style trackers — labels data and
refuses to let it reach a sink it shouldn't, at zero runtime cost. The same idea, on this engine, is one
*instance* of a more general construction: a security **lattice** (a proved `enum` of levels) plus a `@Label` on
each source and sink. The verifier discharges the **noninterference** obligation —
`leq( join(ΓE(e), PC), L(sink) )` — over the class's *own* lattice, by the same Z3 backend that proves the
contracts. No new solver theory; the obligation is just a lattice formula. (The Γ/lattice encoding follows Smith,
[*A Dafny-based approach to thread-local information flow analysis*](https://staff.itee.uq.edu.au/smith/recent/dafny.pdf),
§III. The paper's concurrent rely/guarantee story is *reconstructed* on the per-thread rely-step model — see the
rely/guarantee section — but the underlying concurrency/atomicity soundness, that threads truly interleave at the
assumed grain, stays a deliberate non-goal.)

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

## Relationship to Groovy's other checkers

groovy-verify is one of a family of `@TypeChecked` extensions, and it deliberately owns a narrow,
deep slice — SMT-backed *functional* verification. A few relationships place it: how its null story
relates to Groovy's existing null tooling, how it composes with the sibling regex and purity checkers
(orthogonally, and cooperatively), and what guards the code its fragment can't yet reach.

### Null handling — three layers, one of them a sibling

Groovy already answers "null" at more than one point in the lifecycle, and it's worth not conflating
them (note especially the runtime `@NullCheck` transform versus the compile-time `NullChecker`):

| Piece | Kind | When | What it does |
|---|---|---|---|
| `@groovy.transform.NullCheck` | AST transform | runtime | injects fail-fast guards on parameters |
| `?.` / `?:` | language operators | runtime | safe-navigation / Elvis |
| **`groovy.typecheckers.NullChecker`** | **type-checking extension** | **compile time** | flow-sensitive nullness via `@Nullable` / `@NonNull` / `@MonotonicNonNull` |
| **groovy-verify** | **type-checking extension** | **compile time** | SMT obligation `recv != null` at each dereference; also *proves* `@NonNull` returns/fields when non-nullness is provable |

The last two are siblings — the same extension SPI — approaching null from opposite ends.
**`NullChecker` is the specialist:** annotation-driven and flow-sensitive (it follows null guards,
early-exit `if (x == null) return`, safe navigation, monotonic fields, non-null-by-default), modelled
on the Checker Framework's Nullness Checker, and it answers *"could this be null here?"* without a
solver. **groovy-verify treats nullity as a by-product** of proving richer properties: it asserts
`¬(recv != null)` and asks Z3, so it catches a dereference when the surrounding logic or a
`@Requires` makes non-nullness *provable* — and returns a refuting input (`g(null, 0)`). It has no
`@Nullable` / `@NonNull` awareness in source positions Groovy's AST surfaces, does not model `?.`, and
makes every named-receiver dereference *and* every indexed-element dereference (`xs[i].method()` /
`xs.get(i).method()`, Phase 37) an unconditional obligation against per-element nullity oracles.
**For dedicated null-safety, reach for `NullChecker`;** the residual boxed-element gap
(`List<@Nullable String>` at the type-use position, which Groovy's AST doesn't reliably surface here)
is exactly what its annotations express.

Because both are just extensions, they **compose** — nullness-by-annotation and SMT functional
verification in a single compile, each doing what it is best at. And there's a clean seam where
groovy-verify proves a condition NullChecker can only *assume*. Even in flow-sensitive `strict` mode,
NullChecker tracks the nullness of **variables** (and annotations); it has no per-**element** nullity model,
so it silently assumes an array element `xs[0]` is non-null. groovy-verify makes that dereference an
obligation `xs[0] != null` against its per-element oracle (Phase 37) — so on the same code it **proves** what
NullChecker assumes, or **refutes** it with a witness:

<!-- doclint:case p-multichecker/nullchecker-strict-verifychecker-per-element-non-null-proven-from-requires -->
```groovy
@TypeChecked(extensions = ['groovy.typecheckers.NullChecker(strict: true)', 'verification.VerifyChecker'])
class C {
    @Requires({ xs != null && xs.length > 0 && xs[0] != null })
    static int firstLen(String[] xs) { xs[0].length() }   // proven safe; strict NullChecker is satisfied too
}
```

Drop the `xs[0] != null` premise and groovy-verify **disproves** the assumption — `Possible
NullPointerException`, counterexample `firstLen([null])` — while strict NullChecker stays silent, its flow
model having no handle on the element. The annotation-driven direction now **composes** too. A `@NonNull`
return is read as an implicit `result != null` postcondition groovy-verify **proves** at the value level —
catching a nullable value that reaches the return through reasoning (arithmetic, contracts, a `@Requires`-only
guarantee) NullChecker's flow model passes over. A `@NonNull` *field* becomes an implicit object invariant
`field != null` that groovy-verify proves *establishment and preservation* for — every constructor leaves it
non-null, no method nulls it — the design-by-contract lifecycle a flow checker doesn't frame. The two don't
double-report: where NullChecker raises an obvious `return null`, groovy-verify skips it as outside its fragment;
`null` passed to a `@NonNull` *parameter*, over source positions groovy-verify doesn't model, stays NullChecker's
to raise. Same extension SPI, complementary ends of the same question.

Both forms in one class (`@NonNull` is any name from NullChecker's set — `@NonNull` / `@NotNull` / `@Nonnull` /
`@MonotonicNonNull`):

<!-- doclint:case nndoc/readme-nonnull-lifecycle-under-both-checkers -->
```groovy
@TypeChecked(extensions = ['groovy.typecheckers.NullChecker', 'verification.VerifyChecker'])
class Greeter {
    @NonNull String name                          // implicit invariant: name != null
    @Requires({ n != null })
    Greeter(String n) { name = n }                // groovy-verify proves the field is *established* non-null
    @NonNull String greet() { 'hi ' + name }      // …and the @NonNull return holds (a concatenation is never null)
}
```

Drop the constructor's `@Requires({ n != null })` and the field can no longer be established non-null —
groovy-verify refutes the implicit invariant with `<init>(null)`; add a `void clear() { name = null }` and it
refutes *preservation* at `clear`. NullChecker, which has no class-invariant lifecycle model, stays silent on
both — the design-by-contract framing is groovy-verify's to supply.

### Two checkers, one regex — syntax beside semantics

When a `.matches` and a sibling's concern meet on the *same* regex, the division of labour is clean:
`RegexChecker` validates the pattern's **syntax**, groovy-verify proves its **semantics** — both in one
compile, each reporting only its own kind of error:

<!-- doclint:case p-multichecker/regexchecker-syntax-verifychecker-semantics-on-the-same-matches -->
```groovy
@TypeChecked(extensions = ['groovy.typecheckers.RegexChecker', 'verification.VerifyChecker'])
class C {
    @Requires({ s != null })
    @Ensures({ result == s.matches("[a-z]+") })               // groovy-verify: result IS the match (str.in_re)
    static boolean isLower(String s) { s.matches("[a-z]+") }   // RegexChecker: the pattern is well-formed
}
```

A typo (`"[a-z+"`) is a **`Bad regex`** from RegexChecker; a false claim about the result
(`@Ensures({ result })`, asserting it always matches) is a **`Cannot prove`** from groovy-verify, over a
pattern RegexChecker has already certified. Neither reaches the other's failure — a malformed regex
isn't a functional bug, and an unprovable postcondition isn't a syntax error. (One seam: RegexChecker
walks method **bodies**, not the generated contract closures, so a regex in `@Requires`/`@Ensures` is
groovy-verify's alone — which is why `isLower` *returns* the match, putting the one pattern where both
can see it.)

### `CombinerChecker` — shape beside semantics

Groovy 6 ships [`CombinerChecker`](https://groovy.apache.org/blog/groovy6-functional), which validates a
combiner's *algebraic shape* — that `injectParallel` / `sumParallel` are handed an **associative** operation, so
partition-and-recombine is safe. For a method reference it **trusts the `@Associative` / `@Reducer` annotation**;
for an inline closure it scans for a non-associative operator (`-`, `/`, `%`, `**`). Same division of labour as
the regex case, one level up: CombinerChecker checks the shape, groovy-verify proves the **semantics** — the
laws actually hold *and* the reduction comes up with the right answer:

<!-- doclint:ignore README illustration: Sum monoid (CombinerChecker + laws) -->
```groovy
@TypeChecked(extensions = ['groovy.typecheckers.CombinerChecker', 'verification.VerifyChecker'])
class Sum {
    @Reducer(zero = '0')                              // Sum is a monoid; CombinerChecker trusts this & checks the seed
    @Ensures({ result == a + b })                     // the combiner's defining equation
    static int add(int a, int b) { a + b }

    @Ensures({ Sum.add(Sum.add(a, b), c) == Sum.add(a, Sum.add(b, c)) })  // associativity, spelled out as a law
    static void associative(int a, int b, int c) { }                      // …but see below — @Reducer makes this redundant

    @Requires({ xs != null && xs.length > 0 })
    @Ensures({ result == xs.sum() })                  // the sequential reduction *gives the sum*
    static int reduce(int[] xs) {
        int acc = xs[0], i = 1
        @Invariant({ 1 <= i && i <= xs.length && acc == xs[0..<i].sum() })
        @Decreases({ xs.length - i })
        while (i < xs.length) { acc = Sum.add(acc, xs[i]); i = i + 1 }
        return acc
    }

    static void parallelReduce() {
        [1, 2, 3, 4].sumParallel(Sum::add)            // CombinerChecker certifies this seedless site (Sum::add is @Reducer)
    }
}
```

`add` proves its defining equation; associativity and identity (`a + 0 == a`) prove as laws; and the sequential
reduction that **calls `Sum.add`** gives exactly `xs.sum()` (`Largest.max` does likewise against `a.max()`, with
a `sumParallel(Largest.&max)` call site).

**The laws come for free from the annotation.** `@Reducer` and `@Associative` don't merely *assert* a monoid —
their own javadoc says *"this annotation asserts the laws; it [checks nothing]"*. groovy-verify now reads the
annotation directly: for any `@Associative`/`@Reducer` combiner with an equational `@Ensures({ result == E })`, it
synthesises and discharges the very laws the annotation claims — associativity for both, plus identity over the
declared `zero` for `@Reducer`. So the hand-written `associative` lemma above is **redundant**; delete it and the
proof still holds, because `@Reducer(zero = '0')` already obliges it:

<!-- doclint:ignore README illustration: Sum monoid (@Reducer auto-proves) -->
```groovy
@TypeChecked(extensions = ['groovy.typecheckers.CombinerChecker', 'verification.VerifyChecker'])
class Sum {
    @Reducer(zero = '0')                              // asserts a monoid — and groovy-verify now *proves* it:
    @Ensures({ result == a + b })                     // associativity AND identity (a+0 == 0+a == a) discharged
    static int add(int a, int b) { a + b }            // from the annotation, no lemma method required

    @Requires({ xs != null && xs.length > 0 })
    @Ensures({ result == xs.sum() })
    static int reduce(int[] xs) {
        int acc = xs[0], i = 1
        @Invariant({ 1 <= i && i <= xs.length && acc == xs[0..<i].sum() })
        @Decreases({ xs.length - i })
        while (i < xs.length) { acc = Sum.add(acc, xs[i]); i = i + 1 }
        return acc
    }

    static void parallelReduce() { [1, 2, 3, 4].sumParallel(Sum::add) }
}
```

A bad annotation now fails loudly: `@Associative` on subtraction refutes with `Cannot prove @Reducer
associativity for combiner sub` (`(a-b)-c ≠ a-(b-c)`), and a wrong `zero` — say `@Reducer(zero = '1')` on a sum —
refutes with `Cannot prove @Reducer identity`. `sumParallel` is the seedless reduction — the simplest call form — and
both the `::` method reference and Groovy's `.&` method pointer work (`Foo::bar` parses to a
`MethodReferenceExpression`, a subtype of the `MethodPointerExpression` CombinerChecker recognises). The two
checkers' error channels stay separate, and the synergy runs *both* ways:

- A **non-associative inline combiner** — `injectParallel(0) { a, b -> a - b }` — is a **`CombinerChecker`**
  error from static shape analysis (groovy-verify never sees it; it carries no contract).
- A **seed that contradicts the declared identity** — `injectParallel(5, Sum.&add)` against `@Reducer(zero =
  '0')` — is a **`CombinerChecker`** error too (the seed still has to be passed: there's no seedless
  `injectParallel` overload, so `@Reducer` buys a *check*, not a shorter call).
- A **falsely-`@Associative` method** — annotate `Minus.sub` as `@Associative` and CombinerChecker *trusts* it
  and stays silent at the `Minus.&sub` call site — but groovy-verify **refutes** the associativity law
  (`(a-b)-c ≠ a-(b-c)`) with a **`Cannot prove`**, catching the false annotation the shape checker cannot.

The loop *calling* the combiner works via **combiner inlining**: a no-`@Requires` method with
`@Ensures({ result == E })` is translated as `E` at its call sites (sound — its `@Ensures` is verified when the
combiner is checked), so `acc = Sum.add(acc, xs[i])` becomes `acc + xs[i]` and matches the inline aggregation
pattern. The parallel recombination = sequential fold is `injectParallel`'s own (associativity-requiring)
contract — which CombinerChecker checks and we prove: the same "prove the local fact, rely on the library's
structural guarantee" shape as the monitor invariant.

### `MonadicChecker` — laws beside shape

The same split, one level up. Groovy 6's `MonadicChecker` validates a **monadic comprehension**'s *shape* — that
the carrier in a `DO(a in m, …) { … }` block participates (has `flatMap`/`map`, or is `@Monadic`) and that the
closures return the right carrier type. For the laws it **trusts the `@Monadic` annotation** — whose own javadoc
says it *"asserts that the carrier is lawful"* and checks nothing. groovy-verify discharges exactly that: from
`@Monadic` + the carrier's `bind`/`map`/`unit`, it synthesises and proves the **monad and functor laws** (left /
right identity, associativity, functor identity / composition) — no hand-written lemmas, the `@Monadic` analogue
of the `@Reducer` story above.

This shape-versus-laws gap is where even the strongest type systems stop. Haskell's `Monad` and Scala's
`cats.Monad` enforce the *shape* — the `>>=`/`flatMap` and `return`/`pure` signatures — but **not the laws**: a
lawless instance (a `flatMap` that drops or reorders effects, breaking associativity or right identity)
type-checks and compiles in both, the laws left as a documented obligation you uphold by convention or, at best,
property-test (QuickCheck / ScalaCheck). Proving them at compile time is exactly what a type system structurally
*can't* do — and it's the line this work is drawn to cross.

A whole-class, *four*-checker compile:

<!-- doclint:case p-fourchecker/readme-maybe-under-four-checkers-do -->
```groovy
@Monadic(bind = 'flatMap', map = 'map')
@TypeChecked(extensions = ['groovy.typecheckers.NullChecker', 'groovy.typecheckers.MonadicChecker',
                           'groovy.typecheckers.PurityChecker', 'verification.VerifyChecker'])
class Maybe {                                              // a hand-rolled Some(value) | None
    final boolean present
    final Object value
    private Maybe(boolean present, Object value) { this.present = present; this.value = value }
    static Maybe some(Object v) { new Maybe(true, v) }     // unit
    static Maybe none()         { new Maybe(false, null) }

    @Requires({ f != null }) Maybe flatMap(Function f) { present ? (Maybe) f.apply(value) : this }
    @Requires({ g != null }) Maybe map(Function g)     { present ? some(g.apply(value)) : this }   // Vavr-style

    static Maybe addPair() { DO(a in some(2), b in some(3)) { some(((Integer) a) + ((Integer) b)) } }
}
```

Each extension does a *distinct* job on the one class: **MonadicChecker** shape-checks the `DO` comprehension,
**PurityChecker** the side-effect freedom the laws assume, **NullChecker** the nullness, and **groovy-verify**
proves the five laws from `@Monadic` alone — all four compile quietly because this `Maybe` *is* lawful.

Unlike the `@Reducer` example above — which spelled out the `associative` lemma in the class before deleting it —
we've kept the laws *out* of `Maybe` here, because `@Monadic` is a heavier annotation and the explicit forms would
swamp the example. But they're the point, so here is exactly what those five obligations would look like written by
hand, as the `@Ensures` lemmas you would otherwise add (`f` / `g` a bind function `Function<Object, Maybe>`, `p` /
`q` a plain map function `Function`):

<!-- doclint:ignore README illustration: monad laws (five laws) -->
```groovy
@Ensures({ some(a).flatMap(f) == f.apply(a) })                                       // left identity
static void leftIdentity(Object a, Function<Object, Maybe> f) { }

@Ensures({ m.flatMap({ x -> some(x) }) == m })                                       // right identity
static void rightIdentity(Maybe m) { }

@Ensures({ m.flatMap(f).flatMap(g) == m.flatMap({ x -> f.apply(x).flatMap(g) }) })  // associativity
static void associativity(Maybe m, Function<Object, Maybe> f, Function<Object, Maybe> g) { }

@Ensures({ m.map({ x -> x }) == m })                                                 // functor identity
static void functorIdentity(Maybe m) { }

@Ensures({ m.map(p).map(q) == m.map({ x -> q.apply(p.apply(x)) }) })                 // functor composition
static void functorComposition(Maybe m, Function p, Function q) { }
```

`@Monadic` synthesises and discharges all five — so, exactly as with the `@Reducer` lemma, none of them needs to
be in the source: the carrier declares `@Monadic` and the laws are proved for it. (Four of these — the identity
and associativity laws — are verified directly as hand-written lemmas in the `P-monadlaw` / `P-maybe` test groups;
functor composition is the discriminator the auto-synthesis proves for the Vavr-style `Maybe` and refutes for the
Optional-style one, next.)

The payoff is the carrier that **isn't**. `java.util.Optional` is famously *almost* a monad: its `flatMap` laws
hold, but `map` **collapses a `null` result to empty** (`ofNullable`), which breaks the functor-composition law —
`m.map(f).map(g) ≠ m.map(f ∘ g)` when `f` returns `null`. Write that `map` (Optional's semantics) instead, with
`@NonNull` content (Optional's contract — `Some` never holds null, which NullChecker enforces and groovy-verify
assumes per parameter):

<!-- doclint:ignore README illustration: Maybe.map (Optional-style) -->
```groovy
    @NonNull final Object value
    @Requires({ g != null })
    Maybe map(Function g) { present ? (g.apply(value) == null ? none() : some(g.apply(value))) : this }
```

…and groovy-verify **refutes** the law the annotation asserts:

```
[Static type checking] - Cannot prove @Monadic functor composition for carrier Maybe
    law: (m.map(p).map(q) == m.map({ x -> q.apply(p.apply(x)) }))
```

Same engine, opposite verdicts: it **proves** the Vavr-style `Maybe` lawful and **disproves** the Optional-style
one — turning "Optional is not a lawful functor" from folklore into a counterexample, while the other three
checkers compose around it. (For a *production* `Option`/`Either`, reach for a library like Vavr or Functional
Java — verifying laws is for the carrier you *build*; the libraries' are trusted and, being bytecode, out of
groovy-verify's source-level reach anyway.)

### `PurityChecker` — discharging a premise groovy-verify relies on

Composition isn't always orthogonal. groovy-verify's pure-function evaluation (Phase 8a) proves a method
by *inlining a contract-free same-class helper as a value* — sound only if that helper is referentially
transparent, which groovy-verify **assumes but never checks**. `PurityChecker` verifies precisely that,
turning the unstated premise into a machine-checked one:

<!-- doclint:case p-multichecker/puritychecker-verifychecker-pure-helper-contract-proven-via-pure-eval -->
```groovy
@TypeChecked(extensions = ['groovy.typecheckers.PurityChecker', 'verification.VerifyChecker'])
class C {
    @groovy.transform.Pure
    static int triple(int n) { 3 * n }            // PurityChecker: provably side-effect-free
    @Ensures({ result == 30 })
    static int f() { triple(10) }                 // groovy-verify: proven by evaluating triple(10)
}
```

Both pass — and `f`'s proof now rests on *checked* purity, not trusted purity. Give `triple` a side
effect (`counter += 1`) and `PurityChecker` names the exact violation (`@Pure violation: field
assignment to 'counter'`) where groovy-verify — unable to evaluate the impure body — would only shrug a
vague `Cannot prove`. This is the deepest of the pairings: one checker underwrites a premise the other
takes on faith.

### Outside the fragment, the code is still guarded

groovy-verify is *loudly* partial: anything outside its fragment is skipped, never silently passed
(see [Non-goals](ROADMAP.md)). Two safety nets mean "skipped" does not mean "unprotected":

- **The contracts still run.** The annotations are stock `groovy.contracts`, so every
  `@Requires` / `@Ensures` / `@Invariant` / `@Decreases` / `@Modifies` that groovy-verify *couldn't*
  discharge at compile time is still enforced as an ordinary **runtime assertion**. A proof we skip
  degrades to a runtime check, not to nothing — and the spec is written once, serving both. Being
  machine-readable and compiler-enforced, those same contracts also read as a specification a human or
  AI agent can reason from without opening the body — even mechanically deriving property-based tests
  (see [*Groovy 6 features for Functional Programmers*](https://groovy.apache.org/blog/groovy6-functional)) — and groovy-verify only sharpens that, since a `@Ensures` it has discharged is *proven*, not merely asserted.
- **Sibling checkers cover orthogonal properties.** The `groovy-typecheckers` module ships a set of
  `@TypeChecked` extensions, each owning a property groovy-verify doesn't model: `NullChecker`
  (nullness), `RegexChecker` (malformed regular expressions), `FormatStringChecker`
  (`printf` / `String.format` argument mismatches), `PurityChecker` / `ModifiesChecker`
  (`@Pure` / `@Modifies` compliance), and others (`CombinerChecker`, `MonadicChecker`, …). The regex and
  purity pairings shown above put two of them to work; the rest compose the same way. Together the
  family checks far more than any one
  extension's fragment.

## Tool knobs

Six environment variables tune what the checker *reports* — never what it proves. They're **transient tooling**,
set per run, distinct from the permanent `@TypeChecked(extensions = …)` configuration; unset, every one leaves the
default path byte-identical.

| knob | what it adds |
|------|--------------|
| `VERIFY_REFUTATION=assert\|junit\|spock` | render a refutation's counterexample as a runnable repro test |
| `VERIFY_SUGGEST=contract` | suggest the `@Requires` that would discharge a refuted implicit obligation |
| `VERIFY_EXPLAIN` | on a *verified* obligation, show which authored `@Requires` clauses the proof used |
| `VERIFY_VERBOSE` | print the full OpenJML-style diagnostic + counterexample behind each one-line result |
| `VERIFY_CACHE_STATS` | print the in-process VC-cache hit / miss ratio |
| `VERIFY_DUMP_SMT` | print every solver query as a self-contained SMT-LIB2 benchmark (pipe to cvc5/z3/yices) |

The first three act on one diagnostic, in three directions. Take an unguarded index access:

<!-- doclint:ignore Tool-knobs walkthrough scaffold — illustrative unguarded method shared by the three knob examples -->
```groovy
static int g(int[] a, int i) { a[i] }   // no guard — the bounds obligation refutes
```

It refutes with a concrete counterexample:

```
[Static type checking] - Possible IndexOutOfBoundsException: index may be out of bounds
    obligation: 0 <= i && i < a.size()
    counterexample: a.size() = 0, i = -1
    fails on: g(new int[0], -1)
```

**`VERIFY_REFUTATION` — counterexample → runnable test.** That `fails on:` line is the default repro — a call to
paste and watch throw. Set `VERIFY_REFUTATION=junit` (or `assert` / `spock`) and the *same* counterexample is
rendered as a self-checking test instead:

```
repro (JUnit):
    @Test void gFails() { assertThrows(IndexOutOfBoundsException.class, () -> C.g(new int[0], -1)); }
```

It's a confirmation bridge, not a keeper. The test is green *while the bug is live* — the call really throws — so
run it to prove the compile-time counterexample is a genuine runtime failure (ruling out a verifier
false-positive). Then fix the bug and **flip the test**: once the call no longer throws, invert the assertion into
a regression — *"this input is now handled"* — or delete it. (A verify-only obligation like integer overflow wraps
silently at runtime, so it has no exception to assert and is shown as documentary.)

**`VERIFY_SUGGEST` — refutation → suggested contract.** The complementary move — not *what input breaks it* but
*what precondition would fix it*. Set `VERIFY_SUGGEST=contract` and the same refutation gains one line:

```
    suggested fix: @Requires({ 0 <= i && i < a.size() })
```

Paste that `@Requires` onto `g` and the bounds obligation discharges — the refutation becomes a proof. This is the
Clousot / CodeContracts abduction angle: the guard is the positive form of the violated check, in your own
spelling (`.size()` vs `.length`). It only fires when that guard is a valid precondition — referencing parameters
and fields, never a local or loop variable — so it pastes verbatim. It's a hint, not an auto-fix (a guarded `if`
or a class invariant is often the better home), and overflow is excluded on purpose: its honest guard depends on
operand signs, and the naive range-check would read vacuously under Groovy's wrapping int arithmetic.

**`VERIFY_EXPLAIN` — proof → the clauses it leaned on.** The third direction runs on the obligations that *pass*.
With `g` now guarded — and, say, slightly over-specified — `VERIFY_EXPLAIN` reports, per verified obligation,
which authored `@Requires` clauses the proof actually used, and which it didn't:

```
@Requires({ i >= 0 && i < a.length && i != 7 })
static int g(int[] a, int i) { a[i] }

explain ✓ a[i] in bounds
    load-bearing:     @Requires (i >= 0)
    load-bearing:     @Requires (i < a.length)
    not load-bearing: @Requires (i != 7)
```

That last line is the payoff: `i != 7` carries no weight for the bound, so a hygiene-minded reader can drop it.
The verdict comes from **ablation** — remove one clause, re-prove at full strength, and a clause is load-bearing
exactly when its removal breaks the proof. Because it never uses Z3's weaker unsat-core mode it explains the
*whole* fragment (quantifier and FP proofs included), and because it's a pure downstream read-out in a fresh
solver it can't change a verify / refute. It's the most interactive of the three — O(n) re-proofs per obligation,
so it's for the method you're studying, not a suite-wide sweep — and it currently covers the bounds and divide
obligations. An obligation discharged without an authored `@Requires` (an inline guard, invariant, or path fact)
says so, rather than inventing a clause.

It looks past your `@Requires`, too. A proof often leans on a **structural** fact you didn't write — a class
invariant, or a JVM integer bound — and those surface as `also leaned on`. On the ring buffer, the bounds proof
for `values[head]` names the hidden dependency:

```
explain ✓ values[head] in bounds
    load-bearing:     @Requires (head < tail)
    also leaned on:   @Invariant (0 <= head && head <= tail && tail <= values.length)
```

— so you learn the access is safe *because of* the invariant; weaken it and the proof breaks. Only load-bearing
structural facts show (a JVM bound that wasn't needed stays quiet), so the dependency that matters isn't lost in
noise.

The other three are operational rather than directional — `VERIFY_VERBOSE` prints the full diagnostic behind each
one-line pass/fail, `VERIFY_CACHE_STATS` reports the VC-cache hit/miss ratio, and `VERIFY_DUMP_SMT` prints every
solver query as a self-contained SMT-LIB2 benchmark (declarations, assumptions, the *negated* goal, `(check-sat)`)
so you can pipe an obligation to another solver for a second opinion or read the exact formula to debug the
encoding. All three, with the gradle invocations, are in [BUILD.md](BUILD.md).

## Building & using

Built with JDK 25 against `org.apache.groovy:6.0.0-SNAPSHOT` from the
[ASF snapshot repository](https://repository.apache.org/content/repositories/snapshots). `./gradlew verify`
runs the compact console suite (one line per case); `./gradlew test` runs the same `CASES` data list as
JUnit 6 dynamic tests, and `./gradlew check` additionally enforces the doc-drift lints. It isn't on Maven
Central yet — consume it via a local install, a Gradle composite build, or JitPack.

The full command set (verbose / cache-stats flags, the single-source `CASES` self-test design, the doc-drift
gate) and the three ways to depend on it live in **[BUILD.md](BUILD.md)**.

## Architecture

The codebase map — the component table, the compile-time pipeline (how
`ContractExpansionTransform` captures contracts at `CONVERSION` *before*
groovy-contracts erases them, the metadata handoff to `VerifyChecker`, and the
`SmtSession` solver seam) — lives in **[ARCHITECTURE.md](ARCHITECTURE.md)**.

## License

Apache-2.0.
