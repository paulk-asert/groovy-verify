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

**Loudly partial, not silently sound.** Verification is sound *within* a deliberately **modest
fragment** — the subset of Groovy it models, grown not by size but by *alignment with the proofs people
actually write* — and **loudly unsound outside it**: anything the encoder can't model emits a "skipped:
outside fragment" diagnostic, never passes silently. The failure
mode the verifier family fears most is a silent *vacuous* pass — a "proof" that succeeds only because its
assumptions can never all hold, so it proves nothing. Saying *loudly partial* directly is the credible
position, and it's the one this tool holds.

**Known limitations — named, not hidden.** Consistent with that, every gap is called out: per capability
in the "deferred"/"residual" notes of the [capability table](#whats-demonstrated), and as the
[ROADMAP](ROADMAP.md)'s non-goals. Three boundaries are worth stating up front. **32-bit overflow** is
**opt-in** via `@CheckOverflow` (Verus parity) — by default integers are unbounded mathematical values.
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
    while (i < n) { i++ }
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

For a property over the *whole* index range there's an even shorter spelling — `a.indices` **is** `0..<a.length`,
so "every element is non-negative" reads `a.indices.every { a[it] >= 0 }`, and that precondition is enough to
prove the in-range access `a[k]` yields a non-negative result:

```groovy
@Requires({ a.indices.every { a[it] >= 0 } && 0 <= k && k < a.length })
@Ensures({ result >= 0 })
static int get(int[] a, int k) { a[k] }
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
contents oracles in **static-single-assignment** (SSA) form — each write mints a fresh name, so a
mutator's pre- and post-states stay distinct — and pairs with a runtime-faithful `xs.count(v)` (see the
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

**Aliasing — the bug value-semantics tools miss.** When two references can point at the *same* object, a write
through one is visible through the other — something lightweight checkers ignore by treating distinct names as
distinct objects. This method *looks* obviously correct:

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

**Set algebra — union, intersection, difference, symmetric difference.** All of Groovy's set operators
verify, with their bitwise-operator aliases: `a + b` / `a | b` (union), `a.intersect(b)` / `a & b`
(intersection), `a - b` (difference) and `a ^ b` (symmetric difference, "in exactly one"). Membership
lowers element-wise, so a policy merge proves what you'd expect — a permission granted by *either* set is
in the union:

```groovy
@Requires({ p in granted })
@Ensures({ p in (granted | extra) })       // granted ∪ extra
static int merge(Set<Integer> granted, Set<Integer> extra, int p) { 0 }
```

The element-wise lowering keeps it honest: `p in a` alone does **not** entail `p in (a ^ b)` — `p` might be
in `b` too, so symmetric difference excludes it — and that claim rightly refutes. The `containsAll` and
materialised forms (`Set u = a + b`, then `u.containsAll(a)`) work over enum-element sets (finite domain)
and Int-element sets under a `Sets.boundedBy` bound.

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
neither side is a constant) is now handled by Z3's non-linear integer arithmetic (NIA), so sign facts
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

**Bitwise and shift operators — at Java's 32-bit width.** `& | ^ << >>` are modelled faithfully. A shift
by a literal is power-of-two arithmetic (`x << 1 == x * 2` proves), while `& | ^` go through Z3's
bit-vector theory, so two's-complement facts hold exactly — here, that the low bit of any `int` is `0` or `1`:

```groovy
@Ensures({ result == 0 || result == 1 })
static int lowBit(int a) { a & 1 }
```

`a ^ a == 0`, `a & a == a`, and `6 & 3 == 2` all prove; a wrong concrete value (`6 & 3 == 3`) refutes. Bit
reasoning is bit-blasted, so a *false symbolic* claim soft-fails to a loud "could not decide" rather than a
counterexample — sound, never a false pass.

**Building arrays — literals and sized allocation.** A method may construct and return an array. A
fixed-arity literal `new int[]{a, b}` (or a list literal `[a, b]` coerced to the `int[]` return) folds its
elements; a sized `new int[n]` is a fresh, Java-zero-filled array, so an unwritten slot reads `0` and a body
store bounds-checks against the length:

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

**Money — conservation, and no fractional cents.** Financial code lives on `BigDecimal`, and the proofs
that matter are about *value not leaking*. `BigDecimal` `+`/`-`/`*` are exact and Z3's Real sort models
exact arithmetic, so a conservation invariant is a *faithful* proof — and it isn't vacuous: skim a cent and
the build fails.

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
(`xs.add(i, v)`, `xs.remove(i)`) still defer — their quantified shift modelling stays out of
fragment.

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
cast because the *seeded* GDK `sum(initial)` overload is declared to return `Object` by signature — this is
*not* an erased generic (those are restored in contract closures by GROOVY-12071), so the cast genuinely
stays where the unseeded `xs.sum()` and other typed accessors no longer need one.

Task 008 (`sum_product`) — return both the sum and the product of a list — exercises *two*
aggregations at once. Sum is `xs.sum()`; product has no GDK method, so the idiom is the fold
`xs.inject(1) { a, x -> a * x }`, which the verifier recognises as a product (`prod$`, the
multiplicative sibling of `sum$`). Both accumulate in one loop, and — returning them as the **typed
pair** HumanEval uses — each is proven against its *own* aggregate:

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

Task 013 (`greatest_common_divisor`) is the **two-argument** sibling: a `Gcd.of(a, b)` helper lowers to a
`gcd$ : (Int, Int) -> Int` constrained by Euclid's defining axioms — base `∀x. gcd(x, 0) == x` and step
`∀x, y. y ≠ 0 ⟹ gcd(x, y) == gcd(y, x % y)`. The iterative Euclid loop verifies against it: the invariant
`Gcd.of(x, y) == Gcd.of(a, b)` is preserved by `t = x % y; x = y; y = t` because the step axiom (`y ≠ 0`
from the loop guard) e-matches `gcd(x, y) == gcd(y, x % y)`; at exit `y == 0` the base axiom collapses
`gcd(x, 0)` to `x`; and it terminates on the variant `y`, since `x % y ∈ [0, y)` for `x ≥ 0, y > 0`:

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

The two operations Z3 has *no* primitive for — `reverse` and case folding — are uninterpreted
functions pinned at the literal level, and they **compose**:

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

### Nested loops — `count = n·n` via a double loop

A loop may sit inside another loop, each carrying its own `@Invariant`/`@Decreases`. The textbook case
accumulates `n·n` by counting `1` across an `n × n` grid:

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

An inner loop may also **fill an array** — the flat `a[i*m + j] = 0` matrix fill verifies end-to-end, with
its nonlinear store bound `i*m + j < n*m` discharged by a verifier-supplied monotonicity lemma (Phase 91b;
see the capability table). Out of fragment, all skipping loudly: a third level of nesting, an inner loop
with no `@Invariant`, or one that grows a collection (`xs.add`).

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
| **Array construction** — fixed-arity literal `new int[]{a, b}` (a positional factory, `result[k]`/`.length` fold) and *sized* allocation `new int[n]` (fresh, Java-zero-filled: `sizeOf == n`, non-null, const-0 contents, so a length spec proves, an unwritten element reads `0`, and a body `r[i] = v` bounds-checks and threads). A coerced list literal `[a, b]` returned as `int[]` works too | `new int[]{…}` / `new int[n]` / `[a,b] as int[]` | ✅ |
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
| **Inline set algebra — union / intersection / difference / symmetric difference** | `(a + b)` or `(a \| b)`, `a.intersect(b)` or `(a & b)`, `(a - b)`, `(a ^ b)` (Groovy overloads the bitwise operators for sets: `\|`=union, `&`=intersection, `^`=symmetric difference). Pointwise membership `x in (a op b)` lowers per-element for any sort (`∨` / `∧` / `a∧¬b` / `xor`); `(a op b).containsAll(u)` lowers over the finite enum domain or — for `Set<Integer>` — a bounded universal on the argument's `Sets.boundedBy(u, n)`. Lazy — no new set handle minted | ✅ Phase 33 |
| **Materialised set ops** | `Set<X> u = a op b` (any of `+` / `.intersect` / `-` / `^`; `as Set<X>` where the GDK returns `Collection`) mints `u` as a first-class set via the membership iff relating it to its operands — enum over the finite domain, `Set<Integer>` over a `Sets.boundedBy` bound that `u` inherits (intersection ⊆ either operand, difference ⊆ a, union/symdiff ⊆ a∪b). Subsequent `u.contains` / `u.containsAll` / `u.size()` and the enum pigeonhole/coverage axioms light up automatically | ✅ Phase 35 |
| **`Map<K, Set<V>>` nesting (read)** | `m[k].contains(x)` / `x in m[k]` / `m[k].containsAll(s)` over `Map<Role, Set<V>>` — the map's value sort is the inner set's characteristic-array sort `Array<V, Int>`, so `m[k]` reads as a transient SMT array (no named handle minted). Inner-set mutation and `m[k].size()` are deferred | ✅ Phase 36 |
| **List element nullability** | `xs[i].method()` and `xs.get(i).method()` are now implicit-NPE-checked against a per-element nullity oracle; `@Requires({ xs[i] != null })` and `if (xs[i] != null) …` guards discharge it. Counterexamples render as `f([null])` / `f([null, null])`. Annotation matching (`@NonNull` / `@NotNull` / `@Nonnull` / `@MonotonicNonNull` simple-name set, à la NullChecker) is plumbed but Groovy's AST doesn't always preserve type-use annotations on generics; use the contract form | ✅ Phase 37 |
| **Immutable container factory recognition** | `List.of(args)` / `Set.of(args)` / `Map.of(k1,v1,…)` and Groovy literals `[a,b,c]` / `[k:v]` (with `as Set` cast for set literals) peephole-fold to ground SMT terms: `.size()` to the literal count, `.contains` / `containsKey` / `containsValue` / `in` to a finite disjunction over the entries, `.get(literal_i)` / `[literal_i]` to the i-th element, `Map.of(…).get(k)` to an ite-chain. A factory bound to a local (`xs = List.of(…)`) lifts the same folds across the variable boundary, pinning nullity and size oracles too. No new handle minted, no axioms emitted | ✅ Phase 38 / 38b |
| **Common list/map method-form idioms** | `xs.get(i)` / `xs.first()` / `xs.head()` / `xs.last()` lower to the existing array-access path (with `IndexSite` synthesised so the bounds check fires the same way as `xs[i]`); `xs.set(i, v)` as a statement threads through the same `ArrayStore` step as `xs[i] = v`; `m.getOrDefault(k, default)` lowers to `ite(m.containsKey(k), m[k], default)`. Sublist-returning idioms (`tail`, `init`, `drop`, `take`) still defer | ✅ Phase 39 |
| **Size-changing list mutation** | `xs.add(v)` (append) threads `newSize = oldSize + 1` and `newArr = store(oldArr, oldSize, v)`; `xs.clear()` sets `newSize = 0`; `xs.removeLast()` / `xs.pop()` thread `newSize = oldSize - 1` with a synthesised `IndexSite(xs, 0)` obligation so pop-on-empty refutes with `fails on: f([])`. Consecutive mutations chain via expression composition (no SSA naming). Shift-based variants (`xs.add(i, v)`, `xs.remove(i)`) still defer | ✅ Phase 40 |
| **Bounded `xs.count(v)` faithful to runtime semantics** | A list's `xs.count(v)` translates to `bcount(arr, v, 0, sizeOf(xs))` — bounded by the *current* size, matching Groovy's GDK semantics. The per-store law fires on `bcount` for List receivers; the boundary law fires on `xs.add(v)` (`+1` if `v` matches) and `xs.removeLast()` (`-1` if dropped tail matches). `xs.add(v); xs.removeLast()` provably preserves `xs.count(v)` — today's headline win. Arrays (`int[]`) keep the unbounded `count` (fixed size, no semantic mismatch) so the permutation sort showcase is untouched | ✅ Phase 41 |
| **Implicit obligations downstream of mutations** | `VfObligation` now carries a single source-ordered step list (Assign / Guard / LemmaCall) replayed via the same handlers `checkPath` uses, so the implicit-obligation pass and the body-replay pass see the same oracle state. `xs.add(v); xs[0]` now passes the implicit bounds check; `xs.removeLast(); xs[n-1]` correctly refutes | ✅ Phase 42 |
| **32-bit integer overflow (opt-in via `@CheckOverflow`)** | A method or class annotated `@CheckOverflow` gets a Verus-style guarantee: every `+`, `-`, `*` (sub-expressions included) becomes an implicit obligation that the math result stays in `[Integer.MIN_VALUE, Integer.MAX_VALUE]`. Unannotated code keeps the math-int default — the verifier's existing experience. Implicit JVM int bounds (size oracles, int parameters, int fields) are *always-on*, asserted from the JVM contract, so the math view and machine view coincide for the common case of in-bounds index arithmetic | ✅ Phase 44 |
| **Cross-class `@Invariant` assumption** | A class-typed parameter carries its class's invariants into the calling method. `c.count >= 0` is assumed automatically when the receiver `c: Counter` has `@Invariant({ count >= 0 })`. Cross-class calls (`c.incr()`) discharge the callee's `@Requires` under a receiver context, then havoc the receiver's fields and re-assume its invariants on return. Field references are namespaced per receiver (`c$count` distinct from `b$count`); for a *single* receiver this is sound under the no-aliasing assumption (a project [non-goal](ROADMAP.md)), and when *two* parameters of the same class are present the identity model below (Phase 89) engages instead — they may alias | ✅ Phase 45 |
| **Reference identity + identity-keyed object fields (reads + writes)** | Two object parameters of the same class are *alias-modelled*: their `int` fields are a per-`(class, field)` heap map indexed by object identity, and `a === b` / `a.is(b)` lowers to identity equality `id(a) == id(b)`. **Reads** (slice 1): `a.is(b)` makes the fields **provably coincide** (`a.is(b) ⟹ a.balance == b.balance`), **refuted without it** — reasoning the per-name model (distinct names ⇒ distinct objects) structurally cannot do. **Writes** (slice 2): `a.balance = v` stores into the map, so a write through `a` is **observed through `b` exactly when they alias** — `a.is(b) ⟹ (a.balance = 100 ⟹ b.balance == 100)`, refuted without the alias. Straight-line, `int`-field-only; single-object-param and distinct-class methods keep the per-name model untouched. **Not pursued** (a dual-tenet boundary): the `old(obj.field)`-relative `transfer` — groovy-contracts' `old` is a `Map` of `this`-field snapshots and never captures a *parameter's* field, so such a contract can't run at runtime; modelling it would be verify-only, breaking the executable-specs principle | ✅ Phase 89 (slices 1–2) |
| **String predicates** | `s.startsWith(p)` / `s.endsWith(q)` / `s.contains(sub)` / `s.isEmpty()` on String-typed receivers translate as uninterpreted Bool functions over the existing `String!Sort`. Two applications with the same arguments share the SMT term, so the predicate composes by syntactic identity across contracts and bodies — adequate for "every filter survivor matched the predicate"-shape reasoning (HumanEval task 029, `filter_by_prefix`). Typed-local non-Int lists (`List<String> r = []`) are co-shipped: the empty factory now mints with the right element sort | ✅ Phase 46a |
| **String length oracle + light axioms** | `s.length()` (and the GDK alias `s.size()`) on a String-typed receiver routes to an uninterpreted `(String) → Int` oracle. String literals are pinned at mint: `"hello"`'s length is asserted as 5, so `"hello".length() == 5` folds. Three universally-quantified axioms ship alongside: `length(s) >= 0` for any String, `startsWith(s, p) ⟹ length(p) <= length(s)`, and the same for `endsWith`. Together they let the verifier prove that a 4-char string *cannot* start with `"hello"`, outright — not just "can't prove either way". `s.isEmpty()` lowers to `length(s) == 0` so the two expressions are interchangeable | ✅ Phase 46b / 46c |
| **In-loop `if`-condition + `&&` short-circuit as path facts** | `dischargeRegion` (which checks implicit obligations across a loop's prefix / guard / body / suffix) now recurses into in-region `if` statements with `cond` (then-branch) or `NotExpression(cond)` (else-branch) added to the assumption set, and descends through `&&`/`||`/ternary so each operand is discharged under the short-circuit guard. A natural in-loop `if (xs[i] != null) xs[i].method()` or `if (xs[i] != null && xs[i].startsWith(p))` discharges the per-element deref directly — the `Forall.range` workaround used in earlier ports is now optional, not required | ✅ Phase 46d |
| **`charAt` with per-position literal pinning and bounds** | `s.charAt(i)` on a String-typed receiver routes to an uninterpreted `(String, Int) → Int` oracle returning the codepoint at position `i`. String literals are pinned per-position at mint: `"hello"` asserts `charAt(0)==104, charAt(1)==101, …`, capped at 64 chars to bound mint cost. A new `StringCharAtSite` synthesises the bounds obligation `0 <= i < s.length()` so out-of-range indices refute with the same `IndexBounds` diagnostic list reads produce. `(int) s.charAt(i)` casts route transparently. *Superseded by Phase 47 (native string theory).* | ✅ Phase 46e |
| **Z3 native string theory** | `declareSort('String')` returns Z3's native `Seq Char` sort, replacing the Phase-27 uninterpreted `String!Sort` and retiring the Phase 46a–c uninterpreted predicates + axioms. `startsWith` / `endsWith` / `contains` / `length` / `charAt` all dispatch to Z3 native primitives (`str.prefixof`, `str.len`, `seq.nth + char.to_int`, etc.); structural cross-string facts like `s.startsWith(t) ∧ i < t.length() ⟹ s.charAt(i) == t.charAt(i)` now verify as free theory consequences. `s + t` (operator) and `s.concat(t)` (method) translate to `str.++`; `s.substring(begin, end)` / `s.substring(begin)` translate to `str.substr` with synthesised bounds obligations. Distinct literals are theory-distinct (no pairwise cascade needed); literal length and per-position content are theory consequences (no mint-time pinning needed). Counterexample rendering uses Z3's native `getString()` | ✅ Phase 47 |
| **`replace`, `indexOf`, regex `matches`** | `s.replace(old, new)` → `str.replace` (first-occurrence; replace-all awaits Z3's `mkReplaceAll` — see the next row for the uninterpreted fallback). `s.indexOf(sub)` and `s.indexOf(sub, fromIndex)` → `str.indexof`. `s.matches(literalRegex)` → `str.in_re` via an inline recursive-descent parser. Composes with `groovy-typecheckers`' `RegexChecker` orthogonally — RegexChecker validates syntax, this checker proves contracts over the regex result | ✅ Phase 47b / 47c |
| **Regex feature expansion** | The Phase 47c parser grew predefined character classes (`\d`/`\w`/`\s` and their negations `\D`/`\W`/`\S`), negated character classes (`[^abc]`/`[^a-z]` via Z3's `mkComplement` + `mkIntersect`), quantified ranges (`{n}`/`{n,m}`/`{n,}` via `mkLoop`), and anchors `^`/`$` as silent no-ops (matches() is already whole-string anchored). Still deferred: word-boundary `\b`, inline flags `(?i)`, backreferences, lookbehind | ✅ Phase 47d |
| **Integer ↔ String conversion (sign-faithful)** | `Integer.toString(n)` / `n.toString()` / `String.valueOf(int)` and `Integer.parseInt(s)`. **Phase 54** threads the sign explicitly (`toString(-7) == "-7"`, not Z3's raw `""`), so the round-trip `parseInt(toString(n)) == n` holds for **all** `n` — closing a silent-unsoundness hole. `parseInt` carries a loud `NumberFormatException` obligation: an unprovably-valid argument refutes rather than silently modelling `-1`. *Residual:* numeral overflow not yet checked | ✅ Phase 47e / 54 |
| **`replaceAll` / `lastIndexOf` (uninterpreted with weak axioms)** | Z3 has no native primitive for either. Phase 47f ships them as uninterpreted functions with two universally-quantified axioms each: `replaceAll` knows non-occurrence is a no-op + same-length swaps preserve length; `lastIndexOf` knows the result is `>= -1` and `== -1` when the substring is absent. Sound under-approximation — proofs that need finer reasoning (e.g. "post-replace charAt matches one of two values") gracefully skip. When Z3 ships `mkReplaceAll`, the uninterpreted form swaps out for native in one edit | ✅ Phase 47f |
| **ASCII case folding (`toUpperCase` / `toLowerCase` / `equalsIgnoreCase`)** | Uninterpreted `toUpper$` / `toLower$` with exhaustive per-literal pinning at mint (`Locale.ROOT` — ASCII-faithful). `"Hello".toUpperCase() == "HELLO"` and `"Hello".equalsIgnoreCase("HELLO")` fold; `equalsIgnoreCase` lowers to `toLower(s) == toLower(t)`; reflexive `s.equalsIgnoreCase(s)` verifies by term identity. Symbolic length-preservation and idempotence aren't reachable (universal axioms tried first but caused Z3 timeouts via seq-theory interaction; dropped in favour of pin-only). Non-ASCII / locale-specific behaviour is the documented gap | ✅ Phase 47g |
| **`String.reverse()` (algebraic, literal pinning)** | The GDK's `reverse()` lowers to an uninterpreted `reverse$ : String → String` with **bidirectional** per-literal pinning at mint (Java `StringBuilder.reverse`) — so `"abc".reverse() == "cba"`, palindrome round-trips, *literal* involution (`"abc".reverse().reverse() == "abc"`) and *literal* length (`"hello".reverse().length() == 5`) all fold as theory consequences, no universals needed. Symbolic algebra (`s.reverse().reverse() == s` / `s.reverse().length() == s.length()` for a variable `s`) is the documented boundary: a probe confirmed the universals that would reach it prove the symbolic cases but poison the refute direction (a false `"abc".reverse() == "abc"` goes from a clean "cannot prove" to a solver timeout), the same seq-`Seq→Seq` stall as case folding | ✅ Phase 47i |
| **GString interpolation** | `"hello $name"` / `"x=${a + b}"` translate to chained `str.++` via the Phase 47 seq theory. Static parts mint as String literals; interpolated values translate as String (when `isStringReceiver` recognises the expression) or pass through `intToString` for the int default. Length composes structurally — `"hello $name".length() == 6 + name.length()` for symbolic `name`. Chained method calls (`"hi $n".startsWith(...)`) route through the existing string-receiver dispatch. Co-shipped: typed local body-scan for `String name = "world"` declarations (skipping groovy-contracts' injected synthetic `result`), sort-aware `bind`, and SSA-fresh-variable sort matching for non-Int locals | ✅ Phase 47h |
| **Non-linear integer arithmetic + integer div/mod** | Phase 8a's pure-NIA opt-out is lifted: `a * b` for two non-literal operands now dispatches through Z3's NIA solver. The per-VC (per verification-condition) 2s timeout protects against the NIA-hang case (UNKNOWN surfaces as "Could not decide" — honest, never silent). Unlocks shapes like `i * i >= 0` (sign reasoning), bounded variable products, `n % 2 == 0` divisibility, and the implicit divide-by-zero obligation fires for `b != 0`. Division/modulo follow **Groovy** semantics (Phase 50) | ✅ Phase 48 / 50 |
| **Groovy-faithful division & modulo** | `/` is `BigDecimal` division (now modelled with Z3's exact Real sort — see below — *not* skipped); `a.intdiv(b)` / `(int)(a / b)` truncate toward zero; `%` / `a.remainder(b)` are sign-of-dividend (`-5 % 2 == -1`); `a.mod(b)` is `BigInteger.mod` (non-negative, with a `b > 0` obligation). Closes the silent Euclidean unsoundness (`@Ensures({ result >= 0 }) a % 3` now refutes) | ✅ Phase 50 |
| **Bitwise / shift operators** | `&` `\|` `^` `<<` `>>` on `int`. Shifts by a non-negative literal stay in unbounded Int arithmetic (`x << k` = `x * 2^k`, `x >> k` = `⌊x / 2^k⌋`, so `(x << 1) == x * 2` proves); `&` `\|` `^` and variable shifts lower to Z3's bit-vector theory at Java's 32-bit width — faithful two's-complement, so `6 & 3 == 2`, `a ^ a == 0`, `a & 1 ∈ {0,1}` prove. Bit-blasted ⇒ timeout-gated and refute-hostile on symbolic claims (a false concrete value refutes crisply; a false symbolic one soft-fails to "could not decide"). `~` / `>>>` out | ✅ |
| **BigDecimal arithmetic as exact reals** | `/` on integers is `BigDecimal` division in Groovy (`5 / 2 == 2.5`, not `2`) — modelled with Z3's exact **Real** sort: int operands coerced via int→real, `BigDecimal` literals and params decimal-typed (only `BigDecimal` — its `+`/`-`/`*` are exact; `double`/`float` are IEEE-754 and take the separate FP path below, *not* the exact-Real one). So `a / 2 == 2.5` proves, `a / 2 == 2` refutes, a `BigDecimal avg(int a, int b)` is provably `(a + b) / 2`, and the full scalar set works — `+ - * /`, unary minus (`-a`), negative literals (`-2.5`), comparisons (Phase 67). Retires the old "`/` skips" caveat; the `b != 0` obligation still fires. *(Out of fragment: `max`/`min`/`abs` over decimal-element collections, and decimal `%`, which skip loudly.)* | ✅ Phase 61 / 67 / 72 |
| **IEEE-754 floating point** (`double`/`float`) | Straight-line `double`/`float` modelled with Z3's **FP theory** — bit-exact with the JVM (RNE rounding, NaN, ±∞, signed zero), the opposite of treating them as exact reals. So the same expression proves in *two* number models: `0.1 + 0.2 == 0.3` for `BigDecimal` (exact) **and** `0.1d + 0.2d != 0.3d` for `double` (IEEE-754). Exact FP facts prove (`0.5d * 2.0d == 1.0d`); full FP arithmetic `+ - * /` (`/` is IEEE division — `x/0.0` is `±Inf`/NaN, *not* a thrown `ArithmeticException`, so it carries no divisor obligation, unlike `BigDecimal` `/`); the high-value class — **no-NaN / finiteness** (`Double.isFinite`/`isNaN`/`isInfinite`) — proves, including over `Math.sqrt`/`Math.abs` (Z3 `fp.sqrt`/`fp.abs`: `x >= 0 ⟹ !isNaN(Math.sqrt(x))`, `Math.abs` non-negative); and it's sound (`(a + b) - b == a` refutes — FP non-associativity; `x == x` refutes — NaN ≠ NaN; unguarded `Math.sqrt` can be NaN). HumanEval 045 `triangle_area` (`a*h/2`) ports here: positive sides prove `result >= 0`, but **not** `result > 0` (tiny sides underflow `a*h` to `+0.0`), and the formula `result == a*h/2` needs a finiteness guard (else NaN breaks `x == x`). Z3 bit-blasts FP, so it's timeout-gated. *(Out of fragment: FP loops, the other transcendentals, tight error bounds.)* | ✅ Phase 73 |
| **`Range.containsWithinBounds(v)`** (all four range forms) | Groovy's *bounds-only* range membership (it ignores the step — what separates it from `contains`) lowers to an interval predicate in `v`'s sort with **no enumeration**, for every range form: closed `a..b`, left-open `a<..b`, right-open `a..<b`, and open `a<..<b` (Groovy 4+ `<..`/`..<`). Each endpoint keeps its own inclusivity (`<` vs `<=`), and the two order-orientations are OR'd so it's exact for forward, reverse *and* equal bounds. Works for a range literal and a `new NumberRange(a,b,step)` / `new IntRange(a,b)` constructor, over Int **and** exact-`BigDecimal` bounds (comparisons ride the per-sort dispatch, so `(1.5<..<4.5).containsWithinBounds(2)` proves via Real). Exact *and* symbolic: a param in `(1,4]` is provably within `(1<..4)` while `x >= 1` alone refutes (the open left needs the strict guard). Pure bounds for every range kind, per the documented `Range` contract (`containsWithinBounds` = "between from and to", distinct from `contains`), so `(2..4).containsWithinBounds(2.5)` proves. (`IntRange.containsWithinBounds` used to delegate to integer-membership `contains` and return `false` here, disagreeing with `NumberRange` for the same interval — fixed in GROOVY-12067; the verifier matches the fixed, pure-bounds runtime.) *(Out of fragment: character/`String` ranges — needs lexicographic order — and `contains`/`==`/`.step`, which need step-aware enumeration; all skip loudly.)* | ✅ Phase 74 |
| **Infinite-stream `every` / `any`** (`iterate` + `limit`/`take`) | A property you *cannot test* — a true `every` over an unbounded `Stream.iterate(seed, f)` never returns. Because these contracts stay **dual** (the same `@Ensures` runs at runtime via groovy-contracts), a `.limit(n)`/`.take(n)` is **required** so the runtime check terminates — and the verifier proves *far past* that spot-check depth. A literal `.limit(N)` **unrolls** to `⋀ₖ P(fᵏ(seed))` (exact — proves the bounded contract the runtime checks; `.any` is the dual `⋁`, a failing element is a counterexample). A **symbolic** `.limit(n)` uses **induction** — `P(seed) ∧ ∀x.(P(x) ⟹ P(f(x)))`, the same base + preservation the loop VCs discharge — proving P for *every* element (so for the runtime's actual `n`, whatever it is): `iterate(0){ k+2 }.limit(n).every{ even }` proves all even, and `iterate(0){ (k+1)%10 }.limit(n).every{ 0 <= it < 10 }` proves bounded-in-`[0,10)` so the `+1` **never overflows** — a fact about element 2³¹ no test reaches. Honest: a monotone `k+1` counter has no finite bound and is **refused**; the base case bites (odd seed refutes "all even"); an **unbounded** terminal `every` (no `.limit`) **skips loudly** rather than bless a contract that would hang at runtime; and the stronger induction encoding fires only in positive goal position (a negated/assumed stream-`every` degrades to the runtime check). Int-element streams; the `iterate`/`limit`/`take` shape is matched structurally (holder-agnostic). | ✅ Phase 75 |
| **`List<BigDecimal>.sum()` + conservation** | A decimal list's contents are an `Array Int Real` and `.sum()` a Real-codomain aggregation (base/step axioms over Z3 Real), so `xs.sum()` proves; a per-store **sum-under-store law** (`sum(store(a,i,v)) == sum(a) - a[i] + v`, for Int *and* Real elements) makes the two compensating sides of a transfer cancel, so `accounts.sum() == old.accounts.sum()` ("no money lost") is proven over a dynamic list. Verify is clean; refuting a violation is the weak direction (sum-axiom timeout → loud "could not decide", not a counterexample) | ✅ Phase 69 / 70 |
| **`xs.max()` / `xs.min()` as a witnessed extremum** (Int, `BigDecimal`, **and** `double`) | A list/array's `max()`/`min()` lowers to a fresh `r` carrying the two defining facts — `r` bounds every element (`∀i. a[i] <= r`) and is achieved by one (`∃i. a[i] == r`, guarded by non-emptiness so `[].max()` can't prove vacuously). `result == a.max()` now means exactly the every/any spec a developer would otherwise write by hand. **Sort-generic** (Phase 76/77): the same `maxMinOf` serves Int, Real (`List<BigDecimal>`), and IEEE-754 (`double[]`) contents, so `.max() >= .min()` proves and composes with the Phase-70 decimal `.sum()`. FP is **not totally ordered**, so the FP extremum's bound/achieved facts are guarded by **all-non-NaN** (Groovy's `max` returns NaN when any element is NaN): a `double[]` `max` bounds every element *under a `!Double.isNaN` precondition*, and **refutes** without it (a NaN element makes `NaN <= max` false). **Scope:** for Int and `BigDecimal` this works both as the `.max()` spec helper *and* as a hand-written witnessed-extremum **loop** verified against it; for **FP it's the `.max()`/`.min()` spec helper only** — a hand-rolled FP max-finding loop fails invariant preservation (FP comparisons are bit-blasted, so the quantifier-instantiation + `<=` transitivity that carries the Int/`BigDecimal` loops doesn't reach an FP loop invariant). *(min/max generalize to every element sort; `sum` stays Int/Real only — IEEE addition is non-associative.)* | ✅ Phase 60 / 76 / 77 |
| **FP-element arrays** (`double[]` / `List<Double>`) | A `double`/`float`-element array's contents are an `Array Int <IEEE sort>` (`sortFor` routes `double → Float64`, `float → Float32` — and **closes the prior trap** where a non-Int element silently defaulted to `Int`). So `xs[i]` reads are FP and comparisons route to the FP theory, and a bounded `∀`/`∃` over the elements instantiates: `(0..<xs.length).every { xs[it] >= 0.0d }` as a precondition lets `xs[0] >= 0.0d` prove; element-to-element and the no-NaN guard above all compose. (`List<Double>` element predicates also type-check in contracts now that GROOVY-12071 restores the closure's generics — `double[]` was previously required to avoid element-type erasure; both work today.) | ✅ Phase 77 |
| **List-literal returns + constant-index `result[k]`** | A method that returns a list literal binds `result` as a fixed-arity **factory container** (size + non-null pinned), so `@Ensures` can reference its elements by *constant* index: `result.size()`, `result[0]`, `result[1]` all fold to the returned elements. This makes the faithful **HumanEval 008 (`sum_product`)** port verify — `return [sum, product]` with `result[0] == xs.sum() && result[1] == …` — where it previously had to collapse to one int for lack of tuple/list returns; a wrong element claim refutes. (Constant index only — heterogeneous symbolic indexing is the `Tuple` story.) | ✅ Phase 78 |
| **`Tuple` / `TupleN` — fixed-arity typed products** | `Tuple.tuple(a, b)` and `new TupleN(a, b, …)` are modelled as fixed-arity factory containers on the Phase-78 foundation, so a returned tuple binds `result` and every accessor folds: named slots `.v1`/`.vN`/`.first`/`.second`/`.getVN()`, constant-index `t[k]`, and `.size()`. **Heterogeneous slots are free** — each slot is a separate AST expression translated in its own sort, so `new Tuple2(1, "hi")` proves `result.v1 == 1 && result.v2 == "hi"` (Int *and* String). **Multiple assignment** `def (a, b) = …` desugars to a temp + per-slot reads, and the bare reassignment / **swap** `(a, b) = [b, a]` on existing locals (Phase 90) snapshots each RHS element before any target is written, so it's a correct *parallel* swap (a sequential outcome refutes). So `sum_product` ports as a *typed* `Tuple2<Integer,Integer>(sum, product)`, and a wrong slot claim refutes. **Tuple parameters** are also modelled (Phase 80): a `Tuple2<A,B> t` param's slots are the caller's values, so `t.v1`/`t.first`/`t[0]`/`t.size()` mint a fresh *typed* entity per slot (`t$vN`, like a Phase-45 object field) — `@Ensures({ result == t.v1 })` resolves, and a heterogeneous `Tuple2<Integer,String>` gives an Int `v1` and a String `v2`. (Constant slot index only — immutable, so no `@Modifies` concerns. Slot *arithmetic* in a contract closure — `t.v1 + t.v2` — type-checks directly now that GROOVY-12071 restores the slot's generic type.) **Component-wise `==`** (Phase 81): `a == b` over two fixed-arity products folds to the conjunction of pairwise component equalities (`!=` the negation; a length mismatch is `false`) — so two tuple params with equal components prove `a == b`, `Tuple.tuple(1,2) != Tuple.tuple(1,3)` proves, and the same fold gives list-literal equality (`[1,2,3] == [1,2,3]`). **Nested tuples** (Phase 82): slot resolution recurses — a constructed `Tuple.tuple(Tuple.tuple(1,2),3).v1.v2` folds through the nested containers, and a nested *param* `Tuple2<Tuple2<A,B>,C> t` flattens `t.v1.v2` to a typed entity `t$v1$v2`. (Nested access `t.v1.v2` resolves in contracts too — the same GROOVY-12071 generics restoration.) | ✅ Phase 79 / 80 / 81 / 82 |
| **Maps as named tuples** (`m.key`) | Groovy's string-named product: a returned/constructed map literal `[sum: s, product: p]` binds `result` as a map factory, and a `Map<String,V>` **parameter** is a Z3 value array — so `m.sum` (property) and `m['sum']` (subscript) both read the value at that key (`m.sum ≡ m['sum']`), in the value sort. So `sum_product` ports as `return [sum: s, product: p]` with `@Ensures({ result.sum == xs.sum() && result.product == … })`, and a map param proves `m.sum == 3 ⇒ result == 3`. Constant keys; a fresh consistent value per key for a param. (With a `Map<String,Integer>` declared type, a value reads back as `Integer` in a contract, so *arithmetic* like `m.x + m.y` type-checks directly — GROOVY-12071.) | ✅ Phase 83 / 84 |
| **Classic `for (init; cond; update)` loops** | A `for` loop with `@Invariant`/`@Decreases` desugars to the existing while-machinery — init threaded into the prefix, `i++`/`i += k` normalised to a plain assignment and appended to the body — so all four loop VCs (establishment / preservation / use / progress) discharge. `.each` stays outside the fragment and skips loudly | ✅ Phase 59 |
| **`do … while` loops** | `do B while (G)` is `B; while (G) B`: the body runs once unconditionally, so the invariant is verified *after* the first iteration (not at entry), while preservation / progress / use are the residual `while` unchanged. This is a **soundness fix** — modelling do-while as a plain while established the invariant pre-body, so a false invariant that was vacuously preserved (guard never true) could "prove" a postcondition the mandatory first iteration violates; the establishment diagnostic is do-while-aware ("…after the do-while's first iteration"). An **early `return` inside the body** is also handled soundly (Phase 88b): since the first iteration runs from the entry state, an in-body exit's `@Ensures` is checked both from there (no invariant/guard assumed) *and* on later iterations — closing a latent unsoundness where the first-iteration exit assumed the not-yet-established invariant | ✅ Phase 88 / 88b |
| **Nested loops (two levels)** | An annotated loop directly inside another annotated loop's body verifies **compositionally**, each loop cut by its own `@Invariant`/`@Decreases`. The outer loop's preservation/progress *summarise* the inner loop — havoc the variables it writes (scalars and **array contents**), then assume `inner_inv ∧ ¬inner_guard` — and the inner loop's own establishment / preservation / progress (and array-index **bounds**) are discharged separately in its context (establishment under `outer_inv ∧ outer_guard`; preservation **not** under `outer_inv`, which is generally false mid-inner-loop, e.g. `count == i*n` while count is changing). So `count = n*n` via a double loop proves end-to-end, and an inner loop may **fill an array** — including a flat *n×m* matrix `a[i*m + j] = 0` carrying `(0..<n*m).every { a[it] == 0 }`. The store's nonlinear bound `i*m + j < n*m` is closed by a **verifier-supplied monotonicity lemma** (Phase 91b): guarded ground facts (`(0≤p ∧ 0≤r) ⟹ 0≤p*r` and `(p<q ∧ 0≤r) ⟹ p*r+r ≤ q*r`) hand Z3 the one nonlinear step it won't take, and content quantifiers are stripped from the bounds discharge (a bound never depends on array contents) to keep Z3 out of its quantifier+NIA dead end — both sound (true facts / fewer assumptions). Soundness rests on the summary being honest: a *too-weak* inner invariant can't sneak a false outer result through (outer preservation fails — the summary leaves the accumulator unconstrained), an out-of-bounds inner store is caught, and an **un-annotated** inner loop, a **size-changing collection mutator** inner loop, or three-deep nesting **skip loudly**. The lemma is still a heuristic — self-products and bounds not reducible to "multiply by a non-negative factor" remain "could not decide" | ✅ Phase 91 |
| **`for (x in xs)` loops** | A for-in over a named Int collection desugars to an *indexed* while: a hidden synthetic index drives iteration, the loop variable keeps its source name (bound to `xs[idx]` each pass) so contracts and counterexamples read in terms of `x`, and an index-bounds invariant + a `size - idx` termination measure are auto-injected (the index isn't user-nameable). Both `for (x in xs)` and `for (T x : xs)` work. For-in over a literal / non-named collection skips | ✅ Phase 63 |
| **For-in invariants over the loop variable** | An `@Invariant` clause that references the loop variable is checked at *body-entry* (with `x` bound to the current element), exactly as groovy-contracts does at runtime — a per-element check, not a loop-head invariant. So `@Invariant({ x >= 0 })` discharges from `@Requires({ xs.every { it >= 0 } })` (Phase 64), an accumulator clause and an element clause can be mixed in one `@Invariant`, and the check is correctly *vacuous* on an empty collection — fixing a false positive where the loop-head check failed on the never-iterated empty case | ✅ Phase 65 |
| **Loop-stable `@Requires` in preservation/progress** | Preservation/progress soundly assume the `@Requires` conjuncts that reference only state the loop body doesn't modify (computed via a write-set analysis; if the body has a construct whose writes can't be bounded, *all* conjuncts are dropped). This unlocks element reasoning over a read-only collection — `xs.every { it >= 0 }` instantiated at the current element proves a running total stays non-negative — while a precondition over a *modified* variable is still correctly dropped (so a loop that decrements `cap` can't assume `cap >= 1000`) | ✅ Phase 64 |
| **Bounded property-based refutation on UNKNOWN** | When the solver can't *decide* a postcondition (a quantifier/recurrence-axiom timeout — the weak refutation direction), a concrete pass runs the executable contract over a small integer grid and reports the first failing input as a best-effort `fails on:` repro (e.g. `result == Fib.of(n)` → `fails on: f(2)`). A *witness*, not a proof of falsity; outside its integer fragment it bails to an honest "could not decide", never a false refutation | ✅ Phase 62 |
| **Early-`return` guards in the loop prefix** | A method with an annotated loop can now lead with the idiomatic `if (cond) return e;` guard pattern — multiple stacked guards work. Each early-exit `if` is partitioned out of the prefix and verified on its own path (assume `¬prior-guards`, sym-exec prior non-exit statements, assume this guard, bind `result`, check `@Ensures`); the loop's establishment / use checks fire with `¬each-prefix-guard` assumed, so the loop machinery only runs on the no-exit path | ✅ Phase 49a |
| **Early-`return` inside the loop body** | An `if (cond) return e;` at the top level of the loop body verifies on its own path (assume invariant ∧ loop-guard, walk body up to this exit interleaving `¬prior-body-guards` with sym-exec of non-exit body statements, assume this guard, bind `result`, check `@Ensures`). Preservation and progress walk the body interleaving `¬each-in-body-guard` (we're on the no-exit-fired path). The `is_prime` HumanEval port now matches the Verus source structurally — prefix guards + in-body returns + NIA bound check, all verifying. Suffix-region exits and exits nested in non-top-level if-branches remain deferred | ✅ Phase 49b |
| **Sum aggregation over a list (Int *and* String)** | `xs[lo..<hi].sum()` (prefix sum, for loop invariants) and `xs.sum()` (whole list) lower to base/step axioms — `sum$(arr,lo,hi)` for an Int list (a running total provably equals the list sum, `s == xs[0..<i].sum()` carried across the loop) and **`strConcat$`** for a `List<String>` (duck-typed `['a','b','c'].sum() == 'abc'`, over the `str.++` monoid). Other element domains skip honestly. The value-sum analogue of `count`/`bcount`. Empty range modelled as `0`/`""` (Groovy's `[].sum()` is `null` — needs a non-empty guard); refuting a false claim returns honest UNKNOWN. HumanEval 3 `below_zero` (`result ⟺ ∃ prefix < 0`) verifies on it | ✅ Phase 51 |
| **Product aggregation via the `inject` fold** | `xs.inject(1) { a, x -> a * x }` (and `xs[lo..<hi]`-ranged) is recognised as a product → `prod$(arr,lo,hi)` with base (empty = 1) / step (`× arr[h-1]`) axioms; `inject(0){ a, x -> a + x }` is the sum fold. A running product proof mirrors the sum loop (preservation closes by congruence, not NIA). HumanEval 8 `sum_product` verifies sum + product in one loop | ✅ Phase 52 |
| **Recursive-sequence specs: `Fib.of(i)` / `Trib.of(i)` / `Gcd.of(a,b)` / `Lcm.of(a,b)`** | Fibonacci (`fib$`: base `0,1`, step `fib(k)=fib(k-1)+fib(k-2)`), tribonacci/`fibfib` (`trib$`: base `0,0,1`, step `trib(k)=trib(k-1)+trib(k-2)+trib(k-3)`), and Euclid's gcd (`gcd$`: base `∀x. gcd(x,0)=x`, step `∀x,y. y≠0 ⟹ gcd(x,y)=gcd(y, x%y)`) spec helpers — the two-/three-term-recurrence and two-*argument* siblings of `sum`/`prod`. The textbook iterative-equals-recursive proof verifies (`result == Fib.of(n)` / `Trib.of(n)`; `result == Gcd.of(a,b)` for Euclid's loop, whose invariant `Gcd.of(x,y) == Gcd.of(a,b)` is preserved by `t=x%y; x=y; y=t` via the step axiom and collapses at exit `y==0` through the base, terminating on the variant `y`). **`Lcm.of(a,b)`** is the multiplicative sibling — `lcm$` built on `gcd$` via the fundamental identity `lcm(a,b)·gcd(a,b)==a·b` — so the identity proves symbolically and `Lcm.of(4,6)==12` unfolds via Euclid (a co-shipped `gcd≠0` axiom lets the `a.intdiv(Gcd.of(a,b))` divide-by-gcd idiom discharge its divisor obligation). These **are** HumanEval **055** (`fib`), **063** (`fibfib`), and **013** (`greatest_common_divisor`); 039's outer `prime_fib` search is a deliberate non-target (open-problem termination). All are **prove-friendly but refute-hostile** — e-matching certifies a true spec fast, but a *false* one (e.g. `Gcd.of(12,8)==5`) only soft-fails on a "could not decide / timeout" because finding a SAT model under an infinitely-instantiable axiom defeats MBQI (still sound — rejected, never a false pass). | ✅ Phase 55 / 63 / 87 |
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
ways to consume `io.github.paulk-asert:groovy-verify:0.1.0-SNAPSHOT`:

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

Verification is sound *within* a deliberately **modest** fragment and **loudly
unsound outside it**: anything the encoder cannot model emits a "skipped"
warning rather than passing silently. It is modest by *intent*, not by size — the
bullets below were each chosen because they line up with proofs people actually
write (bounds, aggregation, sortedness, state machines, recurrences), not to chase
a coverage metric. In expressions the fragment is:

- integer `+`, `-`, `*` (variable products dispatch to Z3's NIA solver under a per-VC timeout, with
  closed subterms folded first; Phase 48), and Groovy-faithful `.intdiv`/`%`/`.mod` (Phase 50); the
  `/` operator is `BigDecimal` division, modelled with Z3's exact **Real** sort (Phase 61) so
  `5 / 2 == 2.5` and `BigDecimal` contracts prove (int operands coerced; only `BigDecimal` is
  exact-Real — `double`/`float` take the IEEE-754 FP path, below); divide-by-zero and
  `.mod`-non-positive obligations fire; `**` is out;
- bitwise / shift operators `& | ^ << >>` (Phase: bitwise) — shifts by a non-negative literal stay in
  unbounded Int arithmetic (`x << k` is `x * 2^k`, `x >> k` is `⌊x / 2^k⌋`), while `& | ^` and variable
  shifts lower to Z3's **bit-vector theory at Java's 32-bit width** (faithful two's-complement; bit-blasted,
  so timeout-gated and refute-hostile on symbolic claims); `~` / `>>>` stay out;
- straight-line `double`/`float` on Z3's IEEE-754 **FP theory** (Phase 73) — bit-exact (NaN, ±∞, RNE),
  with `Math.sqrt`/`Math.abs`; `0.1d + 0.2d != 0.3d` and no-NaN/finiteness prove, FP loops/transcendentals
  skip;
- `xs.max()` / `xs.min()` as the witnessed-extremum spec — `r` bounds every element and is achieved by one
  of them, so `result == a.max()` means what you'd write by hand — over Int (Phase 60), `BigDecimal`/Real
  (Phase 76) **and** `double` lists/arrays (Phase 77, guarded all-non-NaN since FP isn't totally ordered);
  `double[]` / `List<Double>` element predicates ride the same FP theory (a hand-written extremum *loop*
  stays Int/`BigDecimal` only — FP comparisons are bit-blasted, so a quantified FP loop invariant doesn't close);
- aggregation specs carried by a loop invariant: `xs.sum()` and the `inject(1){ a, x -> a * x }` product fold
  (Phases 51/52) over Int and `String` (concatenation on the `str.++` monoid), and `List<BigDecimal>` decimal
  sums with N-account *conservation* (`bal.sum() == old.bal.sum()`; Phases 68–70); the recurrence spec helpers
  `Fib.of(i)` / `Trib.of(i)` / `Gcd.of(a, b)` / `Lcm.of(a, b)` lower to axiomatised primitives (Phases 55/63/87);
- `String` on Z3's native theory of strings (Phase 47): predicates (`startsWith` / `endsWith` / `contains` /
  `isEmpty`), `length` / `size` / `charAt` / `substring` / `indexOf`, composition (`+` / `concat` / `replace` /
  regex `matches`) and GString interpolation, plus `Integer.toString` / `parseInt` conversion and
  the uninterpreted (literal-pinned / weak-axiom) ops `toUpperCase` / `toLowerCase` / `replaceAll` /
  `reverse` (Phase 47i — `"abc".reverse() == "cba"` and literal involution fold; symbolic algebra stays out);
- array construction: a fixed-arity literal `new int[]{a, b}` (the array dual of a list literal — folds
  `result[k]` / `.length` / component-wise `==`) and a sized allocation `new int[n]` (a fresh, Java-zero-filled
  array: `sizeOf == n`, non-null, const-0 contents, so an unwritten element reads `0` and a body store
  bounds-checks); an `int[]`-typed return accepts a coerced list literal `[a, b]` or `new int[]{a, b}` (Phase 78);
- structured returns and products: a list-literal return binds `result` for constant-index `result[k]`
  (Phase 78); `Tuple` / `TupleN` fixed-arity typed products with `.vN` slot access, tuple parameters and
  component-wise `==` (Phases 79–82); and Groovy's map-as-named-tuple (`return [sum: s, …]`, `result.sum`;
  Phases 83/84) — generic-typed component accessors keep their declared type in the contract closure
  (GROOVY-12071), so *arithmetic* and *ordering* on a slot / map value / generic-list element type-check with
  no cast;
- infinite-stream `every` / `any` over `Stream.iterate(seed, f)` with a required `.limit(n)` / `.take(n)`: a
  literal limit *unrolls*, a symbolic limit proves the property of *every* element by induction (base +
  preservation); an unbounded terminal `every` skips loudly (Phase 75);
- `(a..b).containsWithinBounds(v)` over all four range forms, as a pure bounds check (Phase 74);
- comparisons (including the spaceship `<=>`, Phase 58), the boolean connectives `&&`/`||`/`!` and logical
  implication `==>` / `.implies()` (Phase 57), and the conditional `?:` — all short-circuit-aware, so a guard's
  left operand protects accesses in its right (`i > 0 && a[i - 1] < a[i]`) and a `?:` branch is checked under
  its condition;
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
  are in for enum-element sets and for Int-element sets under `Sets.boundedBy(t, n)`; the full
  **set algebra** — union (`a + b` / `a | b`), intersection (`a.intersect(b)` / `a & b`), difference
  (`a - b`) and symmetric difference (`a ^ b`) — is in both *inline* (`x in (a op b)`, `containsAll` on a
  binop receiver) **and *materialised*** (`Set<X> u = a op b` mints `u` as a first-class set with the
  membership iff axiom), for enum-element sets (finite domain) and Int-element sets (`Sets.boundedBy` bound);
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
tracked in SSA so a mutator's pre/post state differ), compound assignment (`+= -= *= /= %=`) and pre/post
`++`/`--` both as statements and **in expression position** (`x = i++` / `x = ++i` / `a[i++] = v` /
`x = a[i++]` — the side-effecting inc/dec is hoisted to its old/new value plus the increment, so the array-fill
loop `while (i < n) a[i++] = 0` verifies and an out-of-bounds `a[i++]` refutes; Phases 85/86), multiple
assignment — both the declaration `def (a, b) = [1, 2]` and the bare parallel **swap** `(a, b) = [b, a]`
(the right-hand side is snapshotted before any target is written; Phases 79 / 90), and an
annotated loop — `while`, `do … while` (Phase 88), a classic
`for (init; cond; update)`, or `for (x in xs)` over a named collection, all desugaring to the same machinery
(Phases 59 & 63; the for-in's index is synthesised and hidden, the loop variable keeps its name; `.each` stays
outside the fragment and skips loudly), **optionally with a second loop nested inside it** (Phase 91, two
levels, scalar accumulators or array-filling inner bodies — see below). A `do … while` is `B; while (G) B` — its body runs once
unconditionally, so the invariant is checked *after* that first iteration, not at entry (modelling it as a
plain `while` was silently unsound — a false invariant established pre-body could prove a wrong spec). Across method boundaries: a callee's `@Ensures` is assumed at its call site, a method-level
`@Decreases` lets the method's own `@Ensures` be assumed at a recursive call (proof by induction — and a
`void` lemma proven once then applied by calling it), and `@Modifies` frames what a call may change so the
caller havocs only those locations while `old.x` snapshots pre-state field and array contents. When the
solver returns *UNKNOWN* on a
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
| `Sets` / `Sorted` / `Fib` / `Trib` / `Gcd` / `Lcm` | runtime-executable spec helpers the encoder recognises, each lowered to an axiomatised primitive — `Sets.boundedBy`/`boundedCount` (cardinality), `Sorted.ascending`/etc. (the flat two-variable sortedness axiom, also reached via the native `xs.isSorted()`), `Fib.of(i)` (Fibonacci), `Trib.of(i)` (tribonacci/`fibfib`), `Gcd.of(a, b)` (Euclid), `Lcm.of(a, b)` (least common multiple, via the gcd identity) |
| `PathFacts` | enclosing-`if` path conditions per expression site |
| `ContractTester` | the bounded property-based fallback (Phase 62): runs the executable contract over a small integer grid when the solver returns *UNKNOWN*, reporting a `fails on:` repro |
| `CheckOverflow` | the opt-in `@CheckOverflow` annotation that turns on 32-bit integer-overflow obligations (Phase 44) |
| `ContractExpansionTransform` / `ContractSource` | global CONVERSION transform capturing verbatim contract text (`requires`/`ensures`/`decreases`/`modifies`) + clean body snapshots onto the runtime `@ContractSource` carrier the checker re-parses |
| `SmtBackend` / `Z3Backend` | the solver seam (`SmtBackend.session()` → `SmtSession`) and its z3-turnkey implementation |
| `Reporter` | OpenJML-style diagnostics with inline counterexamples |

`Encoder` is written against the `SmtSession` interface; `Z3Backend` is the only
concrete binding, so an alternative solver is a drop-in.

## License

Apache-2.0.
