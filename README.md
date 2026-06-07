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

**Loudly partial, not silently sound.** Verification is sound *within* a deliberately small
**fragment** — the subset of Groovy it can model — and **loudly unsound outside it**: anything the
encoder can't model emits a "skipped: outside fragment" diagnostic, never passes silently. Specific gaps are named per
capability (the "deferred"/"residual" notes in the [capability table](#whats-demonstrated) and the
[ROADMAP](ROADMAP.md)); 32-bit integer overflow is covered opt-in via `@CheckOverflow` (Verus
parity); heap aliasing is a deliberate [non-goal](ROADMAP.md). The failure mode the verifier family fears most is a silent *vacuous*
pass — a "proof" that succeeds only because its assumptions can never all hold, so it proves nothing.
Saying *loudly partial* directly is the credible position, and it's the one this tool holds.

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

## Examples

Each snippet below is compiled under `@TypeChecked(extensions = 'verification.VerifyChecker')`,
so the proofs run at **compile time**. The contracts are stock `groovy.contracts`
annotations, so the same `@Requires`/`@Ensures`/`@Invariant` still execute as ordinary
runtime checks when verification is off.

**Postconditions — the contract is the spec.** Z3 proves the body satisfies `@Ensures`:

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

```groovy
@Requires({ n >= 0 })
@Ensures({ result == n })
static int countUp(int n) {
    int i = 0
    @Invariant({ 0 <= i && i <= n })
    @Decreases({ n - i })
    while (i < n) { i = i + 1 }
    return i
}
```

The same machinery handles **aggregation** — and running totals are a classic source of *silently
wrong* answers (an off-by-one or a forgotten element yields a plausible-but-wrong number, with no
exception to flag it). Here the loop invariant carries a *prefix sum* `xs[0..<i].sum()` (the idiomatic
Groovy spelling), so the returned value is *proven* equal to the whole-list sum:

```groovy
@Requires({ xs != null && xs.size() > 0 })
@Ensures({ result == xs.sum() })
static int total(List<Integer> xs) {
    int s = xs[0]
    int i = 1
    @Invariant({ 1 <= i && i <= xs.size() && s == xs[0..<i].sum() })
    @Decreases({ xs.size() - i })
    while (i < xs.size()) { s = s + xs[i]; i = i + 1 }
    return s
}
```

Under the hood the solver is told just two facts about `sum` — the sum of an empty range is `0`, and
extending a range by one element adds that element — which is exactly enough to prove the body's
`s = s + xs[i]` keeps `s == xs[0..<i].sum()` true on every iteration. (The non-empty guard reflects a
real Groovy semantic: `[].sum()` is `null`, not `0`.)

**Properties over whole arrays — in the idiom you'd already write.** This is how you turn a *latent*
assumption like "this method only works on a sorted array" into one the compiler enforces — so passing
unsorted input is a build error, not a surprise at runtime. The contract is a plain `.every { … }`
(a "for all" over the elements); a *sorted* precondition (every element ≤ its successor) lets the
checker conclude adjacent elements are ordered, and because it's ordinary GDK Groovy it runs as a
runtime check too:

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

**Lists and boxed types — same reasoning, same syntax.** The encoder never inspects whether a value
is `int` or `Integer`, or whether a sequence is an `int[]` or a `List` — it models every integer type
as a mathematical integer and any subscripted, sized receiver as its contents. So `max` above proves
identically declared `Integer max(Integer a, Integer b)`, and the sorted-`diff` holds verbatim over a
`List<Integer>`, in the same idiom (`xs[i]`, `xs.size()`):

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

```groovy
@Requires({ xs.size() > 0 && xs[0] != null })
static int firstLen(List<String> xs) { xs[0].length() }
```

Drop the `xs[0] != null` guard and the refutation pins a concrete failing input. The Java-style
method idioms `xs.get(i)` / `xs.first()` / `xs.head()` / `xs.last()` / `xs.set(i, v)` lower
through the same array-access machinery (with the bounds check synthesised so `xs.first()` on a
possibly-empty list refutes with `fails on: f([])` exactly as `xs[0]` would). Size-changing
mutation — `xs.add(v)`, `xs.removeLast()` / `xs.pop()`, `xs.clear()` — threads the size and
contents oracles SSA-style and pairs with a runtime-faithful `xs.count(v)` (see the
"Lists — mutation" beat below); only the shift-based variants (`xs.add(i, v)`, `xs.remove(i)`)
still defer. Immutable-container factories (`List.of(...)`, `[a, b, c]`, `Map.of`, …) **are** in,
peephole-folding to ground SMT terms on `.size()`, `.contains`, `.get(literal_i)`, and the same
folds lift across a local: `xs = List.of(1, 2, 3); xs[1]` proves `result == 2`.

**Object state — instance fields, valid by construction.** Not just static functions: a method may
read and update its receiver's fields, and the checker threads field state across the write (so
the contract's entry `count` and exit `count` are different values, related by the assignment).
A class invariant declares the bound once — every constructor proves it *at exit* (the receiver
is valid by construction), and every method assumes it at entry and re-proves it at exit:

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

**String-keyed sets and maps, with the same machinery.** Sets and maps work over `Set<Integer>` /
`Map<Integer,Integer>` and likewise over `Set<String>` / `Map<String,Integer>` (and the enum
variants), the only change being the element sort the encoder uses — every contract idiom
(`x in s`, `s.size()`, `m["k"]`) reads the same. The cardinality law carries across: a fresh-element
add raises the size by one, refuted if the add isn't fresh:

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

**State machines — every state handled, machine-checked.** A `Set<State>` over an `enum` has a
finite domain the verifier exploits: the pigeonhole `handled.size() <= 3` is automatic for any
`Set<State>` (a 3-state enum), and the iff `Sets.boundedCount(handled, N) == N ⟺ every enum constant ∈
handled` is asserted on the set's first use. So an FSM-completeness claim becomes a one-line
contract:

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

**Bugs caught at compile time — with a counterexample and a runnable repro.** The implicit
safety obligations (bounds, divide-by-zero, null) need no annotation; an access the checker
can't prove safe fails the build the way the JVM would name it, plus an input that triggers it:

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

**32-bit integer overflow — Verus-style precision when you want it.** Anything in the fragment is
encoded as Z3's mathematical (unbounded) Int by default — the experience that makes most existing
proofs work. Methods (or classes) that annotate `@CheckOverflow` opt into a stronger guarantee:
every `+`, `-`, `*` becomes an implicit obligation that the math result stays in
`[Integer.MIN_VALUE, Integer.MAX_VALUE]`, refuted otherwise with a runnable repro:

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

Method-level math-int reasoning (no annotation) is preserved verbatim — the entire existing test
suite continues to verify unchanged, and the permutation-sort showcase still uses the unbounded
`int[].count(v)`. `@CheckOverflow` is **additive**: it puts groovy-verify in the same
machine-integer-precision territory as Verus or Dafny without forcing the typed-narrow ergonomic
that limits adoption — *math by default, machine precision on demand.*

**Arithmetic that matches Groovy — including the surprises.** Two things here trip up real code.
First, **`/` on integers is `BigDecimal` division in Groovy** — `5 / 2 == 2.5`, not `2` — so the
verifier models it that way and won't pretend a spec assuming `5 / 2 == 2` is correct (integer
division is `a.intdiv(b)` or `(int)(a / b)`). Second, *variable* multiplication (`a * b` where
neither side is a constant) is now handled by Z3's non-linear integer arithmetic, so sign facts
(`i * i >= 0`), divisibility (`n % 2 == 0`), and bounded products verify directly:

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

**Putting it all together — a fully verified sort.** Everything above composes into one result: a
recursive in-place insertion sort proven **sorted *and* a permutation of its input** — the two halves of
sorting correctness — with no loops; the recursion *is* the proof, and the array is mutated in place under a
sound `@Modifies` frame (across each call the checker *havocs* the array — conservatively forgets everything
it knew about its contents — and re-derives what it needs from the callee's `@Ensures`, so nothing is
assumed unchanged for free).

> **Soundly, under Phase 24.** The recursive call `insert(m-1, a[m], v)` passes the pivot `a[m]` as the new,
> tight bound — so its precondition needs the *transitive* bound `a[it] <= a[m-1]` for all `it`, which Z3
> can't get from *adjacent* sortedness by e-matching. A one-line **monotone-bound lemma** (`maxBound`, proved
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

**Lists — mutation under a sound `@Modifies`, with count preservation faithful to Groovy's runtime.**
A `List<Integer>` is the indexed sibling of the Set: contents under array theory + a size oracle
that threads through every size-changing call. `xs.add(v)` stores at the new last index and
grows the size by one; `xs.removeLast()` / `xs.pop()` shrink (refuted on empty via a synth'd
bounds-check obligation); `xs.clear()` zeros the size and every tracked count. The bounded
`bcount(arr, v, 0, size)` matches Groovy's GDK `xs.count(v)` faithfully across all three, so a
stack-shaped push-then-pop *provably* preserves the count:

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
(`xs.add(i, v)`, `xs.remove(i)`) still defer — their quantified shift modelling is the next
hard slice.

**Finite maps — a value array plus a key-set.** A `Map<Integer,Integer>` is modelled as its values
(`m[k]` / `m.get(k)`, an array) together with its key domain (`m.containsKey(k)` / `k in m`, a *set*).
A `m.put(k,v)` does both — stores the value and adds the key — so value reads, the key frame, and the
key-set cardinality law all hold at once; and because the key-set is the Phase-16 set, `m.size()`
drives the same DFS-shaped recursive measure over a map's key domain:

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

```groovy
class C {
    Map<Integer,Integer> next   // functional graph: successor of node u
    Set<Integer> visited
    int n                       // node domain 0..<n
    @Requires({ 0 <= u && u < n && (0..<n).every { 0 <= next[it] && next[it] < n } })
    @Modifies({ this.visited })
    @Decreases({ fuel })
    @Ensures({ (0..<n).every { (it in old.visited) ==> (it in visited) } &&   // soundness: visited only grows
               (fuel <= 0 || (u in visited)) })                               // progress: u gets visited
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

> *The next four beats build the verified DFS up from its parts — the counting machinery that proves the
> traversal both **terminates** and **visits every reachable node**. This is the deepest material in the
> README (the kind of proof the Dafny/Verus community uses as a benchmark credential); if you'd rather see
> the tool applied to everyday problems, skip ahead to the [HumanEval Examples](#humaneval-examples).*

**The cardinality axiom — `Sets.boundedBy`.** The uninterpreted set size (Phase 16) knows only its per-mutation
deltas — it has no link to *which* elements a set holds. `Sets.boundedBy(s, n)` supplies the **pigeonhole**
relationship for a set whose elements live in a finite domain `[0, n)`: it means exactly `s ⊆ [0, n)`, and
lowers to `s.size() <= n && (s.size() < n || (0..<n).every { it in s })` — a faithful boolean definition over
the cardinality and a bounded membership universal (no trusted axiom). From it the engine *derives* the two
facts cardinality-driven search rests on:

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

**Two gaps remain at this point in the narrative** — *completeness* (every reachable node visited) and
*unconditional* `start ∈ visited` (without a fuel budget). Both are closed by what follows: the
bounded-sum cardinality unlocks the latter, and the frontier/stack invariant lands the former.

**Bounded-sum cardinality — `bcount`, earned by induction.** The genuine count of a set's members in a
domain, `bcount(s,k) = Σ_{i<k} (i ∈ s ? 1 : 0)`, is just an ordinary recursive method — and its foundational
properties are proved by the framework's *own* induction (`@Decreases` on `k`, the self-`@Ensures` as the
hypothesis), no built-in axiom:

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

```groovy
class C {
    Map<Integer,Integer> next         // functional graph
    Set<Integer> visited
    int n
    @Requires({ 0 <= u && u < n && (0..<n).every { 0 <= next[it] && next[it] < n } })
    @Modifies({ this.visited })
    @Decreases({ n - Sets.boundedCount(visited, n) })          // strictly decreases — the per-add law
    @Ensures({ (u in visited) &&                         // ← UNCONDITIONAL coverage
               (0..<n).every { (it in old.visited) ==> (it in visited) } })
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

Task 030 — filter a list to its positive elements:

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

Task 003 (`below_zero`) — detect whether a running balance ever goes negative — is the
**sum-aggregation** showcase, and the spec is the *full biconditional*: the result is true iff
**some prefix sum is negative**.

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
cast because the GDK `sum()` is typed `Object`, so a `< 0` comparison won't type-check without it.

Task 008 (`sum_product`) — return both the sum and the product of a list — exercises *two*
aggregations at once. Sum is `xs.sum()`; product has no GDK method, so the idiom is the fold
`xs.inject(1) { a, x -> a * x }`, which the verifier recognises as a product (`prod$`, the
multiplicative sibling of `sum$`). Both accumulate in one loop, each proven against its aggregate:

```groovy
@Requires({ xs != null && xs.size() > 0 })
@Ensures({ result == ((int) xs.sum()) + ((int) xs.inject(1) { a, x -> a * x }) })
static int sumPlusProduct(List<Integer> xs) {
    int s = xs[0], p = xs[0], i = 1
    @Invariant({ 1 <= i && i <= xs.size() &&
                 s == xs[0..<i].sum() && p == xs[0..<i].inject(1) { a, x -> a * x } })
    @Decreases({ xs.size() - i })
    while (i < xs.size()) { s = s + xs[i]; p = p * xs[i]; i = i + 1 }
    return s + p
}
```

(HumanEval returns a *tuple*; groovy-verify doesn't model tuple/array returns, so this returns
`s + p` to expose both in one int — the point is the two aggregations composing.) The duck-typed
`sum()` also covers concatenation — `['a','b','c'].sum() == 'abc'` over a `List<String>` lowers to
the same base/step machinery on the `str.++` monoid, so a running concatenation verifies just like
the numeric running total.

Task 039's inner `is_prime` — the canonical NIA-plus-control-flow benchmark — ports
verbatim to the Verus source shape:

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

Task 039's *outer* `prime_fib` (the n-th number that is both prime and Fibonacci) is a clean example
of a **deliberate non-target**: it's an unbounded `while true` search whose termination depends on the
*open* question of whether infinitely many Fibonacci primes exist — no `@Decreases` can exist (even
Verus leaves task 039 a `TODO`). But the Fibonacci generation it rests on *does* verify — the textbook
iterative-equals-recursive proof, via a `Fib.of(i)` spec helper (the two-term-recurrence sibling of
`xs.sum()`):

```groovy
@Requires({ n >= 0 })
@Ensures({ result == Fib.of(n) })
static int fibIter(int n) {
    int a = 0, b = 1, i = 0
    @Invariant({ 0 <= i && i <= n && a == verification.Fib.of(i) && b == verification.Fib.of(i + 1) })
    @Decreases({ n - i })
    while (i < n) { int t = a + b; a = b; b = t; i = i + 1 }
    return a
}
```

`Fib.of(i)` lowers to an uninterpreted `fib$` with base/step axioms; the invariant carries the
recurrence `a == fib(i) ∧ b == fib(i+1)`, re-established across `b = a + b` by the step axiom — so the
loop is proven to compute the recursive definition. (The `verification.Fib` FQN inside `@Invariant` is
the same closure-scope wart `Forall` carries.)

Task 029 (`filter_by_prefix`) — same shape, with `s.startsWith(p)` substituted for the
positivity check — ports with the same `result.size() <= xs.size()` spec and the natural
in-body null guard `if (xs[i] != null && xs[i].startsWith(prefix))`. Phase 46d threads the
short-circuit `&&` and any enclosing in-loop `if` as path facts during obligation discharge,
so the inner deref obligation discharges under the guard the conjunction establishes — just
like a straight-line method's `if (s != null) s.method()` shape. Reverse-style benchmarks
port on the `List<Character>` API today; a true `String.reverse()` proof would need its
own uninterpreted+axioms layer (Z3 has no `str.reverse` primitive).

**The string methods you use every day — now provable, not just asserted.** Because they map to Z3's
built-in theory of strings (rather than being treated as opaque), a contract over them can be *proven*:
predicates (`startsWith` / `endsWith` / `contains` / `isEmpty`), indexing (`length` / `charAt` /
`substring` / `indexOf`), composition (`+` / `concat` / `replace` / regex `matches`), and
conversion (`Integer.toString` / `parseInt`) all route to Z3 seq-theory primitives;
`toUpperCase` / `toLowerCase` / `equalsIgnoreCase` / `replaceAll` / `lastIndexOf` are
shipped as uninterpreted functions with literal pinning and weak axioms where Z3 doesn't
ship a primitive yet; GString interpolation (`"hello $name"`) folds to chained `str.++`.
Literals fold to ground constants, out-of-range indices refute with the standard
`IndexBounds` diagnostic, and **structural cross-string facts** like
`s.startsWith(t) ∧ i < t.length() ⟹ s.charAt(i) == t.charAt(i)` come free from the theory.
Composing several in one method:

```groovy
@Requires({ s != null && s.startsWith("user:") })
@Ensures({ result == s.length() - 5 })
static int idLength(String s) { s.substring(5).length() }
```

That verifies via two theory consequences chained — `startsWith ⟹ length(prefix) <= length(s)`
gives `s.length() >= 5`, and `substring(s, 5, k).length() == k` gives the identity. A second
showcase blending regex, GString interpolation, and the structural concat facts:

```groovy
@Requires({ name != null && name.matches("[a-zA-Z]+") })
@Ensures({ result.startsWith("Hi, ") && result.endsWith(name) })
static String greet(String name) { "Hi, $name" }
```

The body folds to `mkConcat(mkString("Hi, "), name)`. Z3's seq theory then knows two
free facts: a literal-prefixed concat starts with that literal (`prefixof(a, a ++ b)`),
and the right operand of the concat is its suffix (`suffixof(b, a ++ b)`). The regex
precondition rides along through whatever shape the body assembles.

The remaining honest gaps: `split` (returns an array, structurally invasive) and symbolic
length-preservation for `toUpperCase` (universal axioms over the seq sort cause Z3 to
hang) remain deferred. The hard NIA corners (general polynomial identities,
square-root / factoring shapes) may time out under Z3's solver — surfaces as "Could not
decide," never silent. Sister task 023 (`strlen`) ports the same way — with the natural
spec `result == xs.size()` added.

## What's demonstrated

The examples above are a slice; here is the full inventory of what the engine proves today, by phase:

| Capability | Authoring | Status |
|---|---|---|
| Preconditions discharged at call sites | `@Requires` | ✅ |
| Postconditions vs. method body | `@Ensures` | ✅ |
| Loop invariants & termination | `@Invariant` / `@Decreases` | ✅ |
| **Array/list index in bounds** | *(implicit)* | ✅ Phase 1 |
| **Division / modulo by zero** | *(implicit)* | ✅ Phase 1 |
| **Null dereference** | *(implicit)* | ✅ Phase 1 |
| **`xs.size()` / `xs.length` / `xs.isEmpty()`** in contracts | `@Requires`/`@Ensures` | ✅ Phase 4 |
| **`x == null` / `x != null`** nullity in contracts | `@Requires`/`@Ensures` | ✅ Phase 4 |
| **`x.equals(y)`** (numeric `==`) | `@Requires`/`@Ensures` | ✅ Phase 4 |
| **`xs.contains(y)`** (precise membership over contents) | `@Requires`/`@Ensures` | ✅ Phase 4 / 9 |
| **Cross-boundary nullity/size at call sites** | `@Requires` | ✅ Phase 4 |
| **Value-flow: safety implied by an assignment** | *(implicit)* | ✅ Phase 5 |
| **Loop-fused bounds (obligation under `@Invariant`)** | *(implicit)* | ✅ Phase 5 |
| **Short-circuit guard path conditions** | `i > 0 && a[i - 1] < a[i]` | ✅ Phase 5 |
| **Bounded-universal quantifiers over arrays** | `Forall.range(lo, hi) { … a[it] … }` | ✅ Phase 6 |
| **Native GDK quantifier idioms** | `(lo..<hi).every{…}`, `xs.indices.every{…}`, `xs.every{ it… }` | ✅ Phase 9 |
| **Existential quantifier (`any`)** | `a.any{ it < 0 }`, `(lo..<hi).any{…}` | ✅ Phase 9 |
| **Array contents: read (`select`) & update (`store`)** | `a[i]` in contracts / `a[i] = v` | ✅ Phase 6 |
| **Array update inside a loop (invariant over contents)** | `a[i] = v` in a `@Invariant`-carrying loop | ✅ Phase 6 |
| **Inter-procedural: assume a callee's `@Ensures`** | `int z = f(args)` | ✅ Phase 7 (slice 1) |
| **Recursion by induction (self-`@Ensures` + termination)** | `@Decreases({ n })` on a method | ✅ Phase 7 (slice 2) |
| **Lemmas: prove a `void` method by induction, call to apply** | `lemma(args)` as a statement | ✅ Phase 7 (slice 3) |
| **Flow-sensitive precondition (use the preceding call's `@Ensures`)** | `sort(a, n-1); insert(a, n-1)` | ✅ Phase 7 (slice 4) |
| **Recursive insertion sort — *sortedness*, end-to-end** | `insert` + `sort` by induction | ✅ Phase 7 |
| **Closed-constant folding (normalise-then-SMT)** | `(2 + 2) * (2 + 2)`, `a[(1 + 1) * 2]` | ✅ Phase 8a (slice 1) |
| **Closed pure-function evaluation** | `pow2(10)`, `factorial(5)` in a contract/body | ✅ Phase 8a (slice 2) |
| **Bounded symbolic unfolding (fuel) + `ite`** | `absV(x)`, `pow2(n)` against a symbolic arg | ✅ Phase 8a (slice 3) |
| **Instance methods & field state (read + write)** | `this.count`, `count = count + 1` | ✅ Phase 10 |
| **Pre-state `old` (field & array-content snapshots)** | `old.count`, `old.a[i]` in `@Ensures` | ✅ Phase 11 |
| **Multiset / `count` preservation (per-store law)** | `a.count(v) == old.a.count(v)` | ✅ Phase 12 |
| **`@Modifies` framing — frame-check + caller-side havoc & sound inter-proc `old`** | `@Modifies({ this.a })` | ✅ Phase 13 |
| **Fully verified in-place sort — *sorted ∧ permutation*** | recursive insertion sort under sound `@Modifies`; recursive precondition discharged soundly via a monotone-bound lemma (Phase 24) | ✅ Phase 14 / 24 |
| **Class `@Invariant` — instance methods (assume on entry, prove on exit, super-walked)** | `@Invariant({ count >= 0 })` on a class | ✅ Phase 15a |
| **Class `@Invariant` — constructors establish the invariant at exit** | `@Invariant({ count >= 0 }) class C { C(int n) { count = n } }` — refutes without `@Requires({ n >= 0 })`. Int fields default-init to 0 to match JVM semantics. | ✅ Phase 15b |
| **Boxed scalars & index-accessed collections** | `Integer`, `Integer[]`, `List<Integer>` via `xs[i]` / `xs.size()` | ✅ (structural) |
| **Finite sets — membership, add/remove, cardinality law** | `x in s` / `x !in s` (negated membership), `s.contains(x)`, `s.add(x)`, `s.size()` over `Set<Integer>` | ✅ Phase 16 |
| **Set-cardinality `@Decreases` measure (DFS-shaped termination)** | `@Decreases({ n - s.size() })` on a recursion that adds a fresh element | ✅ Phase 16 |
| **Finite maps — lookup, key membership, put, key-set cardinality law** | `m[k]`, `m.get(k)`, `k in m`, `m.containsKey(k)`, `m.put(k,v)`, `m.size()` over `Map<Integer,Integer>` | ✅ Phase 17 |
| **Reachability — recursive graph traversal: visited grows (soundness) + node covered (progress)** | DFS over a `Map<Node,Node>` graph marking a `Set<Node>`, fuel- or cardinality-terminated | ✅ Phase 18 |
| **Cardinality axiom — pigeonhole over a bounded domain** | `Sets.boundedBy(s, n)` ⇒ `s.size() <= n`, full ⇒ covers `[0,n)`, a hole ⇒ not full | ✅ Phase 19 |
| **Bounded-sum cardinality `bcount(s,k)` — bound & full-count, earned by induction** | recursive `bcount`; `0 <= bcount(s,k) <= k` and `(0..<k).every{it in s} ⇒ bcount==k` | ✅ Phase 20 |
| **`Sets.boundedCount(s,k)` primitive + per-add law** | a set mutation threads the bounded count: a fresh in-domain `add` raises `Sets.boundedCount(s,k)` by one | ✅ Phase 21 |
| **Full-characterization `count==k ⟺ covers [0,k)` — and end-to-end DFS unconditional coverage** | `Sets.boundedCount(s,k)==k ⇒ u in s`; a cardinality-terminating DFS proves `start ∈ visited` with no fuel bound | ✅ Phase 22 |
| **Completeness — closure ⇒ EVERY reachable node visited** | inductive `propagate` over the chain; `mark` breaks closure (boundary) | ✅ Phase 23 / 25 |
| **Call-site precondition soundness** | intervening mutations threaded, fresh callee formals, early-return narrowing — a precondition is checked at the *state at the call* | ✅ Phase 24 |
| **Recursive definitions in contracts** | a recursive `chain(u,d)`/`bcount(s,k)` carries its defining equation across a lemma boundary (shared symbol + bounded-depth eq) | ✅ Phase 25 |
| **DFS establishes closure — the frontier/stack invariant** | recursion-stack `Set` ghost (push/pop), closed-except-on-stack ⇒ full closure when the stack empties | ✅ Phase 26 |
| **Non-Int element domains — `String` and `Enum` across sets, maps, lists** | `Set<String>`/`Set<Color>`, `Map<String,Integer>`/`Map<Color,V>`, `List<String>`/`List<Color>`; `Color.RED in s`, `m["admin"]==5`, `xs[k]=="abc"`; counterexamples render the model value as a Groovy literal | ✅ Phase 27 |
| **`EnumClass.values().length` / `.size()` folds to a ground int** | `@Requires({ k < Color.values().length })` becomes `k < 3` at translate time — usable as a literal in contracts, bounded-range upper bounds, and ground state-coverage proofs | ✅ Phase 28 |
| **`Sets.boundedBy` / `Sets.boundedCount` over enum-element sets** | `Sets.boundedCount(handled, State.values().length) == State.values().length ⟹ State.IDLE in handled && State.RUNNING in handled && State.DONE in handled` — FSM completeness verified directly with `Set<State>`; pigeonhole `card(s) <= N` automatic on every enum set | ✅ Phase 29 |
| **Subset reasoning — `s.containsAll(t)` over enum-element sets** | `granted.containsAll(required) && r in required ⟹ r in granted` (authorization shape); reflexivity, transitivity, and empty-subset cases all verify; complemented by the empty iff `card(s) == 0 ⟺ no enum constant ∈ s` | ✅ Phase 30 |
| **Subset over Int-element sets via `Sets.boundedBy(t, n)`** | Same `containsAll` shape, now for `Set<Integer>` when the subset operand has a registered bound; the bounded universal `∀i. 0<=i<n ⟹ (i ∈ t ⟹ i ∈ s)` closes via Z3 e-matching on `(select t i)` and `(select s i)` | ✅ Phase 31 |
| **`m.containsValue(v)` for enum-keyed maps + `s.equals(t)` for sets** | `m[State.RUNNING] == 42 ⟹ m.containsValue(42)` (existential over enum keys); `s.equals(t) ≡ s.containsAll(t) ∧ t.containsAll(s)` composes subset both ways | ✅ Phase 32 |
| **Inline set union / intersection** | `(a + b).contains(x)` → `x ∈ a ∨ x ∈ b`; `a.intersect(b).contains(x)` → conjunction; `(a + b).containsAll(u)` for enum sets via finite conjunction. Lazy lowering — no new set handle is minted | ✅ Phase 33 |
| **Materialised set ops** | `Set<X> u = a + b` (or `as Set<X>` on `a.intersect(b)`) mints `u` as a first-class set: subsequent `u.contains` / `u.containsAll` / `u.size()` reasoning, the enum-domain pigeonhole/full-coverage iff/empty iff axioms, and the per-element membership iff relating `u` to its operands all light up automatically | ✅ Phase 35 |
| **`Map<K, Set<V>>` nesting (read)** | `m[k].contains(x)` / `x in m[k]` / `m[k].containsAll(s)` over `Map<Role, Set<V>>` — the map's value sort is the inner set's characteristic-array sort `Array<V, Int>`, so `m[k]` reads as a transient SMT array (no named handle minted). Inner-set mutation and `m[k].size()` are deferred | ✅ Phase 36 |
| **List element nullability** | `xs[i].method()` and `xs.get(i).method()` are now implicit-NPE-checked against a per-element nullity oracle; `@Requires({ xs[i] != null })` and `if (xs[i] != null) …` guards discharge it. Counterexamples render as `f([null])` / `f([null, null])`. Annotation matching (`@NonNull` / `@NotNull` / `@Nonnull` / `@MonotonicNonNull` simple-name set, à la NullChecker) is plumbed but Groovy's AST doesn't always preserve type-use annotations on generics; use the contract form for now | ✅ Phase 37 |
| **Immutable container factory recognition** | `List.of(args)` / `Set.of(args)` / `Map.of(k1,v1,…)` and Groovy literals `[a,b,c]` / `[k:v]` (with `as Set` cast for set literals) peephole-fold to ground SMT terms: `.size()` to the literal count, `.contains` / `containsKey` / `containsValue` / `in` to a finite disjunction over the entries, `.get(literal_i)` / `[literal_i]` to the i-th element, `Map.of(…).get(k)` to an ite-chain. A factory bound to a local (`xs = List.of(…)`) lifts the same folds across the variable boundary, pinning nullity and size oracles too. No new handle minted, no axioms emitted | ✅ Phase 38 / 38b |
| **Common list/map method-form idioms** | `xs.get(i)` / `xs.first()` / `xs.head()` / `xs.last()` lower to the existing array-access path (with `IndexSite` synthesised so the bounds check fires the same way as `xs[i]`); `xs.set(i, v)` as a statement threads through the same `ArrayStore` step as `xs[i] = v`; `m.getOrDefault(k, default)` lowers to `ite(m.containsKey(k), m[k], default)`. Sublist-returning idioms (`tail`, `init`, `drop`, `take`) still defer | ✅ Phase 39 |
| **Size-changing list mutation** | `xs.add(v)` (append) threads `newSize = oldSize + 1` and `newArr = store(oldArr, oldSize, v)`; `xs.clear()` sets `newSize = 0`; `xs.removeLast()` / `xs.pop()` thread `newSize = oldSize - 1` with a synthesised `IndexSite(xs, 0)` obligation so pop-on-empty refutes with `fails on: f([])`. Consecutive mutations chain via expression composition (no SSA naming). Shift-based variants (`xs.add(i, v)`, `xs.remove(i)`) still defer | ✅ Phase 40 |
| **Bounded `xs.count(v)` faithful to runtime semantics** | A list's `xs.count(v)` translates to `bcount(arr, v, 0, sizeOf(xs))` — bounded by the *current* size, matching Groovy's GDK semantics. The per-store law fires on `bcount` for List receivers; the boundary law fires on `xs.add(v)` (`+1` if `v` matches) and `xs.removeLast()` (`-1` if dropped tail matches). `xs.add(v); xs.removeLast()` provably preserves `xs.count(v)` — today's headline win. Arrays (`int[]`) keep the unbounded `count` (fixed size, no semantic mismatch) so the permutation sort showcase is untouched | ✅ Phase 41 |
| **Implicit obligations downstream of mutations** | `VfObligation` now carries a single source-ordered step list (Assign / Guard / LemmaCall) replayed via the same handlers `checkPath` uses, so the implicit-obligation pass and the body-replay pass see the same oracle state. `xs.add(v); xs[0]` now passes the implicit bounds check; `xs.removeLast(); xs[n-1]` correctly refutes | ✅ Phase 42 |
| **32-bit integer overflow (opt-in via `@CheckOverflow`)** | A method or class annotated `@CheckOverflow` gets a Verus-style guarantee: every `+`, `-`, `*` (sub-expressions included) becomes an implicit obligation that the math result stays in `[Integer.MIN_VALUE, Integer.MAX_VALUE]`. Unannotated code keeps the math-int default — the verifier's existing experience. Implicit JVM int bounds (size oracles, int parameters, int fields) are *always-on*, asserted from the JVM contract, so the math view and machine view coincide for the common case of in-bounds index arithmetic | ✅ Phase 44 |
| **Cross-class `@Invariant` assumption** | A class-typed parameter carries its class's invariants into the calling method. `c.count >= 0` is assumed automatically when the receiver `c: Counter` has `@Invariant({ count >= 0 })`. Cross-class calls (`c.incr()`) discharge the callee's `@Requires` under a receiver context, then havoc the receiver's fields and re-assume its invariants on return. Field references are namespaced per receiver (`c$count` distinct from `b$count`), so two parameters of the same type carry independent state. Sound under the no-aliasing assumption (a project [non-goal](ROADMAP.md)) | ✅ Phase 45 |
| **String predicates** | `s.startsWith(p)` / `s.endsWith(q)` / `s.contains(sub)` / `s.isEmpty()` on String-typed receivers translate as uninterpreted Bool functions over the existing `String!Sort`. Two applications with the same arguments share the SMT term, so the predicate composes by syntactic identity across contracts and bodies — adequate for "every filter survivor matched the predicate"-shape reasoning (HumanEval task 029, `filter_by_prefix`). Typed-local non-Int lists (`List<String> r = []`) are co-shipped: the empty factory now mints with the right element sort | ✅ Phase 46a |
| **String length oracle + light axioms** | `s.length()` (and the GDK alias `s.size()`) on a String-typed receiver routes to an uninterpreted `(String) → Int` oracle. String literals are pinned at mint: `"hello"`'s length is asserted as 5, so `"hello".length() == 5` folds. Three universally-quantified axioms ship alongside: `length(s) >= 0` for any String, `startsWith(s, p) ⟹ length(p) <= length(s)`, and the same for `endsWith`. Together they let the verifier prove that a 4-char string *cannot* start with `"hello"`, outright — not just "can't prove either way". `s.isEmpty()` lowers to `length(s) == 0` so the two expressions are interchangeable | ✅ Phase 46b / 46c |
| **In-loop `if`-condition + `&&` short-circuit as path facts** | `dischargeRegion` (which checks implicit obligations across a loop's prefix / guard / body / suffix) now recurses into in-region `if` statements with `cond` (then-branch) or `NotExpression(cond)` (else-branch) added to the assumption set, and descends through `&&`/`||`/ternary so each operand is discharged under the short-circuit guard. A natural in-loop `if (xs[i] != null) xs[i].method()` or `if (xs[i] != null && xs[i].startsWith(p))` discharges the per-element deref directly — the `Forall.range` workaround used in earlier ports is now optional, not required | ✅ Phase 46d |
| **`charAt` with per-position literal pinning and bounds** | `s.charAt(i)` on a String-typed receiver routes to an uninterpreted `(String, Int) → Int` oracle returning the codepoint at position `i`. String literals are pinned per-position at mint: `"hello"` asserts `charAt(0)==104, charAt(1)==101, …`, capped at 64 chars to bound mint cost. A new `StringCharAtSite` synthesises the bounds obligation `0 <= i < s.length()` so out-of-range indices refute with the same `IndexBounds` diagnostic list reads produce. `(int) s.charAt(i)` casts route transparently. *Superseded by Phase 47 — `charAt` is now native, structural cross-string facts now hold* | ✅ Phase 46e |
| **Z3 native string theory** | `declareSort('String')` returns Z3's native `Seq Char` sort, replacing the Phase-27 uninterpreted `String!Sort` and retiring the Phase 46a–c uninterpreted predicates + axioms. `startsWith` / `endsWith` / `contains` / `length` / `charAt` all dispatch to Z3 native primitives (`str.prefixof`, `str.len`, `seq.nth + char.to_int`, etc.); structural cross-string facts like `s.startsWith(t) ∧ i < t.length() ⟹ s.charAt(i) == t.charAt(i)` now verify as free theory consequences. `s + t` (operator) and `s.concat(t)` (method) translate to `str.++`; `s.substring(begin, end)` / `s.substring(begin)` translate to `str.substr` with synthesised bounds obligations. Distinct literals are theory-distinct (no pairwise cascade needed); literal length and per-position content are theory consequences (no mint-time pinning needed). Counterexample rendering uses Z3's native `getString()` | ✅ Phase 47 |
| **`replace`, `indexOf`, regex `matches`** | `s.replace(old, new)` → `str.replace` (first-occurrence; replace-all awaits Z3's `mkReplaceAll` — see the next row for the uninterpreted fallback). `s.indexOf(sub)` and `s.indexOf(sub, fromIndex)` → `str.indexof`. `s.matches(literalRegex)` → `str.in_re` via an inline recursive-descent parser. Composes with `groovy-typecheckers`' `RegexChecker` orthogonally — RegexChecker validates syntax, this checker proves contracts over the regex result | ✅ Phase 47b / 47c |
| **Regex feature expansion** | The Phase 47c parser grew predefined character classes (`\d`/`\w`/`\s` and their negations `\D`/`\W`/`\S`), negated character classes (`[^abc]`/`[^a-z]` via Z3's `mkComplement` + `mkIntersect`), quantified ranges (`{n}`/`{n,m}`/`{n,}` via `mkLoop`), and anchors `^`/`$` as silent no-ops (matches() is already whole-string anchored). Still deferred: word-boundary `\b`, inline flags `(?i)`, backreferences, lookbehind | ✅ Phase 47d |
| **Integer ↔ String conversion (sign-faithful)** | `Integer.toString(n)` / `n.toString()` / `String.valueOf(int)` and `Integer.parseInt(s)`. **Phase 54** threads the sign explicitly (`toString(-7) == "-7"`, not Z3's raw `""`), so the round-trip `parseInt(toString(n)) == n` holds for **all** `n` — closing a silent-unsoundness hole. `parseInt` carries a loud `NumberFormatException` obligation: an unprovably-valid argument refutes rather than silently modelling `-1`. *Residual:* numeral overflow not yet checked | ✅ Phase 47e / 54 |
| **`replaceAll` / `lastIndexOf` (uninterpreted with weak axioms)** | Z3 has no native primitive for either. Phase 47f ships them as uninterpreted functions with two universally-quantified axioms each: `replaceAll` knows non-occurrence is a no-op + same-length swaps preserve length; `lastIndexOf` knows the result is `>= -1` and `== -1` when the substring is absent. Sound under-approximation — proofs that need finer reasoning (e.g. "post-replace charAt matches one of two values") gracefully skip. When Z3 ships `mkReplaceAll`, the uninterpreted form swaps out for native in one edit | ✅ Phase 47f |
| **ASCII case folding (`toUpperCase` / `toLowerCase` / `equalsIgnoreCase`)** | Uninterpreted `toUpper$` / `toLower$` with exhaustive per-literal pinning at mint (`Locale.ROOT` — ASCII-faithful). `"Hello".toUpperCase() == "HELLO"` and `"Hello".equalsIgnoreCase("HELLO")` fold; `equalsIgnoreCase` lowers to `toLower(s) == toLower(t)`; reflexive `s.equalsIgnoreCase(s)` verifies by term identity. Symbolic length-preservation and idempotence aren't reachable (universal axioms tried first but caused Z3 timeouts via seq-theory interaction; dropped in favour of pin-only). Non-ASCII / locale-specific behaviour is the documented gap | ✅ Phase 47g |
| **GString interpolation** | `"hello $name"` / `"x=${a + b}"` translate to chained `str.++` via the Phase 47 seq theory. Static parts mint as String literals; interpolated values translate as String (when `isStringReceiver` recognises the expression) or pass through `intToString` for the int default. Length composes structurally — `"hello $name".length() == 6 + name.length()` for symbolic `name`. Chained method calls (`"hi $n".startsWith(...)`) route through the existing string-receiver dispatch. Co-shipped: typed local body-scan for `String name = "world"` declarations (skipping groovy-contracts' injected synthetic `result`), sort-aware `bind`, and SSA-fresh-variable sort matching for non-Int locals | ✅ Phase 47h |
| **Non-linear integer arithmetic + integer div/mod** | Phase 8a's pure-NIA opt-out is lifted: `a * b` for two non-literal operands now dispatches through Z3's NIA solver. The per-VC 2s timeout protects against the NIA-hang case (UNKNOWN surfaces as "Could not decide" — honest, never silent). Unlocks shapes like `i * i >= 0` (sign reasoning), bounded variable products, `n % 2 == 0` divisibility, and the implicit divide-by-zero obligation fires for `b != 0`. Division/modulo follow **Groovy** semantics (Phase 50) | ✅ Phase 48 / 50 |
| **Groovy-faithful division & modulo** | `/` is `BigDecimal` division (now modelled with Z3's exact Real sort — see below — *not* skipped); `a.intdiv(b)` / `(int)(a / b)` truncate toward zero; `%` / `a.remainder(b)` are sign-of-dividend (`-5 % 2 == -1`); `a.mod(b)` is `BigInteger.mod` (non-negative, with a `b > 0` obligation). Closes the silent Euclidean unsoundness (`@Ensures({ result >= 0 }) a % 3` now refutes) | ✅ Phase 50 |
| **BigDecimal division as exact reals** | `/` on integers is `BigDecimal` division in Groovy (`5 / 2 == 2.5`, not `2`) — modelled with Z3's exact **Real** sort: int operands coerced via int→real, `BigDecimal`/`Double`/`Float` literals and params decimal-typed. So `a / 2 == 2.5` proves, `a / 2 == 2` refutes, and a `BigDecimal avg(int a, int b)` is provably `(a + b) / 2`. Retires the old "`/` skips" caveat; the `b != 0` obligation still fires | ✅ Phase 61 |
| **`xs.max()` / `xs.min()` as a witnessed extremum** | An Int list/array's `max()`/`min()` lowers to a fresh `r` carrying the two defining facts — `r` bounds every element (`∀i. a[i] <= r`) and is achieved by one (`∃i. a[i] == r`, guarded by non-emptiness so `[].max()` can't prove vacuously). `result == a.max()` now means exactly the every/any spec a developer would otherwise write by hand | ✅ Phase 60 |
| **Classic `for (init; cond; update)` loops** | A `for` loop with `@Invariant`/`@Decreases` desugars to the existing while-machinery — init threaded into the prefix, `i++`/`i += k` normalised to a plain assignment and appended to the body — so all four loop VCs (establishment / preservation / use / progress) discharge. `for`-in and `.each` stay outside the fragment (no index to bind the invariant to) and skip loudly | ✅ Phase 59 |
| **Bounded property-based refutation on UNKNOWN** | When the solver can't *decide* a postcondition (a quantifier/recurrence-axiom timeout — the weak refutation direction), a concrete pass runs the executable contract over a small integer grid and reports the first failing input as a best-effort `fails on:` repro (e.g. `result == Fib.of(n)` → `fails on: f(2)`). A *witness*, not a proof of falsity; outside its integer fragment it bails to an honest "could not decide", never a false refutation | ✅ Phase 62 |
| **Early-`return` guards in the loop prefix** | A method with an annotated loop can now lead with the idiomatic `if (cond) return e;` guard pattern — multiple stacked guards work. Each early-exit `if` is partitioned out of the prefix and verified on its own path (assume `¬prior-guards`, sym-exec prior non-exit statements, assume this guard, bind `result`, check `@Ensures`); the loop's establishment / use checks fire with `¬each-prefix-guard` assumed, so the loop machinery only runs on the no-exit path | ✅ Phase 49a |
| **Early-`return` inside the loop body** | An `if (cond) return e;` at the top level of the loop body verifies on its own path (assume invariant ∧ loop-guard, walk body up to this exit interleaving `¬prior-body-guards` with sym-exec of non-exit body statements, assume this guard, bind `result`, check `@Ensures`). Preservation and progress walk the body interleaving `¬each-in-body-guard` (we're on the no-exit-fired path). The `is_prime` HumanEval port now matches the Verus source structurally — prefix guards + in-body returns + NIA bound check, all verifying. Suffix-region exits and exits nested in non-top-level if-branches remain deferred | ✅ Phase 49b |
| **Sum aggregation over a list (Int *and* String)** | `xs[lo..<hi].sum()` (prefix sum, for loop invariants) and `xs.sum()` (whole list) lower to base/step axioms — `sum$(arr,lo,hi)` for an Int list (a running total provably equals the list sum, `s == xs[0..<i].sum()` carried across the loop) and **`strConcat$`** for a `List<String>` (duck-typed `['a','b','c'].sum() == 'abc'`, over the `str.++` monoid). Other element domains skip honestly. The value-sum analogue of `count`/`bcount`. Empty range modelled as `0`/`""` (Groovy's `[].sum()` is `null` — needs a non-empty guard); refuting a false claim returns honest UNKNOWN. HumanEval 3 `below_zero` (`result ⟺ ∃ prefix < 0`) verifies on it | ✅ Phase 51 |
| **Product aggregation via the `inject` fold** | `xs.inject(1) { a, x -> a * x }` (and `xs[lo..<hi]`-ranged) is recognised as a product → `prod$(arr,lo,hi)` with base (empty = 1) / step (`× arr[h-1]`) axioms; `inject(0){ a, x -> a + x }` is the sum fold. A running product proof mirrors the sum loop (preservation closes by congruence, not NIA). HumanEval 8 `sum_product` verifies sum + product in one loop | ✅ Phase 52 |
| **Recursive-sequence spec: `Fib.of(i)`** | a Fibonacci spec helper lowering to `fib$` with base (`0`,`1`) / step (`fib(k)=fib(k-1)+fib(k-2)`) axioms — the two-term-recurrence sibling of `sum`/`prod`. The textbook iterative-equals-recursive proof verifies (`result == Fib.of(n)`). HumanEval 39's outer `prime_fib` search is a deliberate non-target (open-problem termination) | ✅ Phase 55 |
| **Logical implication — `==>` operator & `.implies()` method** | Groovy 5's `a ==> b` (a BinaryExpression) and the DGM `a.implies(b)` both lower to `!a ∨ b` (the backend's `implies`). Frame conditions read naturally — `every { it != j ==> a[it] == old.a[it] }` — and modus ponens / DFS "closed-except-on-stack" invariants simplify. (Eager, like the method; the short-circuit-obligation path for a body-level `==>` guarding an access is a residual — use `if` there) | ✅ Phase 57 |
| **Spaceship operator `<=>`** | `a <=> b` (Int) lowers to the three-way sign `ite(a<b, -1, ite(a==b, 0, 1))` — exactly `Integer.compareTo`'s `-1/0/1` — so a `compareTo`/`compare` method's three-way contract verifies. Int-oriented like the other comparisons; a `String <=>` (lexicographic) skips (would need Z3 string ordering) | ✅ Phase 58 |

## Building & testing

Built using JDK 25. It builds against `org.apache.groovy:6.0.0-SNAPSHOT` from the
[ASF snapshot repository](https://repository.apache.org/content/repositories/snapshots) —
it relies on some fixes due for release in the next Groovy 6 pre-release.

```sh
./gradlew verify                       # compile a battery of good/bad snippets and assert diagnostics
VERIFY_VERBOSE=1 ./gradlew verify      # also print the counterexamples for refuted cases
VERIFY_CACHE_STATS=1 ./gradlew verify  # also print the in-process VC cache hit / miss ratio
```

The self-test ([`src/test/groovy/VerifyHarness.groovy`](src/test/groovy/VerifyHarness.groovy))
compiles annotated snippets on the fly and asserts that good ones verify and
bad ones fail with the expected diagnostic. A process-wide VC cache (Phase 34) keys
Z3 results on the canonicalised asserted-set so suite-wide duplicates skip the solver;
the suite currently rebates ~18 % wall-clock at a 20 % hit rate.

## Using it in your own build

It isn't on Maven Central yet, but you don't need to wait for that — there are three
ways to consume `au.com.asert:groovy-verify:0.1.0-SNAPSHOT`:

- **Local install.** `./gradlew publishToMavenLocal` drops the jar into your `~/.m2`;
  then add `mavenLocal()` and the dependency to any Gradle/Maven project.
- **Composite build (source dependency).** Clone this repo alongside yours and add
  `includeBuild('../groovy-verify')` to your `settings.gradle` — Gradle substitutes the
  dependency with this project's output, so changes here are picked up without a publish.
  (The companion *groovy6-functional* repo consumes it this way.)
- **JitPack.** Because the build is self-contained (ASF snapshot, no local patch), JitPack
  can build it straight from a GitHub tag/commit — add the JitPack repo and depend on
  `com.github.<owner>:groovy-verify:<tag>`, no publishing step on your side.

Either way the consumer compiles under `@TypeChecked(extensions = 'verification.VerifyChecker')`;
the artifact carries Z3 (via z3-turnkey, native libs bundled) on the compile classpath.

## The fragment

Verification is sound *within* a deliberately small fragment and **loudly
unsound outside it**: anything the encoder cannot model emits a "skipped"
warning rather than passing silently. In expressions the fragment is:

- integer `+`, `-`, `*` (variable products dispatch to Z3's NIA solver under a per-VC timeout, with
  closed subterms folded first; Phase 48), and Groovy-faithful `.intdiv`/`%`/`.mod` (Phase 50); the
  `/` operator is `BigDecimal` division, modelled with Z3's exact **Real** sort (Phase 61) so
  `5 / 2 == 2.5` and decimal-typed contracts prove (int operands coerced; `BigDecimal`/`Double`/`Float`
  literals and params are decimal); divide-by-zero and `.mod`-non-positive obligations fire;
  `**`/bitwise are out;
- `xs.max()` / `xs.min()` over an Int list/array (Phase 60), as the witnessed-extremum spec — `r`
  bounds every element and is achieved by one of them — so `result == a.max()` means what you'd write
  by hand;
- comparisons, the boolean connectives `&&`/`||`/`!`, and the conditional `?:` — all
  short-circuit-aware, so a guard's left operand protects accesses in its right
  (`i > 0 && a[i - 1] < a[i]`) and a `?:` branch is checked under its condition;
- the size / nullity / membership oracles from the table above
  (`xs.size()`, `x == null`, `xs.contains(y)`, `x.equals(y)`, `isEmpty()`);
- array/list contents under Z3's array theory (`a[i]` reads, `a[i] = v` updates) with
  bounded-universal quantifiers — `Forall.range` or the native GDK idioms
  `(lo..<hi).every{…}` / `xs.indices.every{…}` / `xs.every{ it… }`;
- finite `Set<Integer>` membership (`x in s`, `s.contains(x)`), mutation (`s.add(x)` /
  `s.remove(x)`, threaded through the body) and cardinality (`s.size()`) — a set is a
  characteristic array, and `size()` carries a per-mutation update law (`add` of an absent
  element raises it by one), which drives a set-valued `@Decreases` measure (`n - s.size()`,
  the DFS-shaped termination argument); subset (`s.containsAll(t)`) and equality (`s.equals(t)`)
  are in for enum-element sets and for Int-element sets under `Sets.boundedBy(t, n)`; union and
  intersection are in both *inline* (`(a + b).contains(x)`, `a.intersect(b).contains(x)`,
  `containsAll` on a binop receiver) **and *materialised*** (`Set<X> u = a + b` mints `u` as a
  first-class set with the membership iff axiom);
- finite `Map<Integer,Integer>` — value lookup (`m[k]`, `m.get(k)`), key membership (`k in m`,
  `m.containsKey(k)`), mutation (`m.put(k,v)` / `m[k] = v`) and size (`m.size()`): a map is a
  value array plus a key-set, so a put both stores the value and adds the key (with the same
  cardinality law), and `m.size()` likewise drives a recursive measure over the key domain;
  `m.containsValue(v)` is in for enum-keyed maps (finite disjunction over key constants);
  **`Map<K, Set<V>>` nesting is in for reads** (`m[k].contains(x)`, `m[k].containsAll(s)`,
  `x in m[k]`) via a nested array sort `Array<K, Array<V, Int>>`; `keySet`/`values` projections
  and nested-set mutation remain outside;
- list element nullability: `xs[i].method()` / `xs.get(i).method()` is an implicit NPE obligation
  against a per-element nullity oracle, discharged by `@Requires({ xs[i] != null })` or an
  `if` guard;
- immutable container factories — `List.of(args)` / `Set.of(args)` / `Map.of(k,v,…)` and Groovy
  literals `[a, b, c]` / `[k: v]` (and `as Set` casts) peephole-fold to ground SMT terms on
  `.size()`, `.contains` / `containsKey` / `containsValue` / `in`, and `.get(literal_i)` —
  and the same folds lift across a local binding (`xs = List.of(…); xs.size()`), with the
  factory's nullity and size pinned on the assignment so implicit checks pass too;
- fuel-bounded inlining of contract-free pure functions (a closed call like
  `pow2(10)` is evaluated to a literal, a symbolic one unfolded);
- scalar instance-field reads (`this.count` / bare `count`) in contracts and bodies.

For method bodies: straight-line code, `if`/`else`, locals and instance fields (re-assignable,
tracked in SSA so a mutator's pre/post state differ), and a single annotated loop — `while` or a
classic `for (init; cond; update)`, which desugars to the same machinery (Phase 59; `for`-in and
`.each` stay outside the fragment and skip loudly). When the solver returns *UNKNOWN* on a
postcondition (a quantifier/recurrence-axiom timeout), a bounded property-based pass runs the
executable contract over a small grid of integer inputs and reports any concrete failing input as a
best-effort `fails on:` repro (Phase 62). See `Encoder` and the roadmap for the exact boundaries.

## Relationship to Groovy's other checkers

groovy-verify is one of a family of `@TypeChecked` extensions, and it deliberately owns a narrow,
deep slice — SMT-backed *functional* verification. Two things place it: how its null story relates
to Groovy's existing null tooling, and what guards the code its fragment can't yet reach.

### Null handling — three layers, one of them a sibling

Groovy already answers "null" at more than one point in the lifecycle, and it's worth not conflating
them (note especially the runtime `@NullCheck` transform versus the compile-time `NullChecker`):

| Piece | Kind | When | What it does |
|---|---|---|---|
| `@groovy.transform.NullCheck` | AST transform | runtime | injects fail-fast guards on parameters |
| `?.` / `?:` | language operators | runtime | safe-navigation / Elvis |
| **`groovy.typecheckers.NullChecker`** | **type-checking extension** | **compile time** | flow-sensitive nullness via `@Nullable` / `@NonNull` / `@MonotonicNonNull` |
| **groovy-verify** | **type-checking extension** | **compile time** | SMT obligation `recv != null` at each dereference |

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
verification in a single compile, each doing what it is best at:

```groovy
@TypeChecked(extensions = ['groovy.typecheckers.NullChecker', 'verification.VerifyChecker'])
```

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
  (nullness), `RegexChecker` (invalid regular expressions caught at compile time), `FormatStringChecker`
  (`printf` / `String.format` argument mismatches), and `PurityChecker` / `ModifiesChecker`
  (`@Pure` / `@SideEffectFree` / `@Contract` side-effect compliance) — the last directly relevant
  here, since groovy-verify's pure-function evaluation (Phase 8a) and `@Modifies` framing (Phase 13)
  *assume* a purity those checkers can actually verify. Others (`CombinerChecker`, `MonadicChecker`, …)
  cover further ground, and they compose the same way. Together the family checks far more than any one
  extension's fragment.

## Architecture

| File | Role |
|---|---|
| `VerifyChecker` | the `@TypeChecked` extension; call-site, body, loop & implicit checks |
| `Encoder` | Groovy expression → SMT (the fragment lives here) |
| `BodyEncoder` / `LoopEncoder` | path enumeration & symbolic execution for `@Ensures`/loops |
| `PureEvaluator` | closed pure-function evaluation & fuel-bounded unfolding — the normalise-then-SMT accelerator (Phase 8a) |
| `Forall` | the `Forall.range(lo, hi){…}` bounded-quantifier helper (the native GDK `every`/`any` idioms are the preferred surface) |
| `Sets` / `Fib` | runtime-executable spec helpers the encoder recognises — `Sets.boundedBy`/`boundedCount` (cardinality) and `Fib.of(i)` (Fibonacci), each lowered to an axiomatised primitive |
| `PathFacts` | enclosing-`if` path conditions per expression site |
| `ContractExpansionTransform` / `ContractSource` | global CONVERSION transform capturing verbatim contract text (`requires`/`ensures`/`decreases`/`modifies`) + clean body snapshots onto the runtime `@ContractSource` carrier the checker re-parses |
| `SmtBackend` / `Z3Backend` | the solver seam and its z3-turnkey implementation |
| `Reporter` | OpenJML-style diagnostics with inline counterexamples |

`Encoder` is written against the `SmtSession` interface; `Z3Backend` is the only
concrete binding, so an alternative solver is a drop-in.

## License

Apache-2.0.
