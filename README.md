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

An SMT-backed verification extension for Groovy, packaged as a standalone
type-checking extension. Annotate code with stock
[`groovy.contracts`](https://github.com/spockframework/groovy-contracts) contracts,
compile a caller under

```groovy
@TypeChecked(extensions = 'verification.VerifyChecker')
```

and Z3 discharges the proof obligations **at compile time** — before the
runtime contract checks would ever fire. Failed proofs surface as ordinary
compile errors with Dafny-style counterexamples.

This started life as the verification spike in the *groovy6-functional* blog
companion repo. It was split out so it can grow on its own; that repo now
consumes it (via a Gradle composite build) rather than vendoring it.

## What's demonstrated

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
| Sort *permutation* (multiset), `@Modifies` framing, class `@Invariant`, 32-bit overflow | — | ⏳ later |

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

**Loop invariants & termination.** The invariant carries the proof across iterations and
`@Decreases` shows the loop ends — so the postcondition `result == n` is *proven of the
computed value*, not assumed. (Recursion is handled the same way: a method-level
`@Decreases` lets the method's own `@Ensures` serve as the inductive hypothesis at the
recursive call.)

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

**Bounded quantifiers over arrays — in the idiom you'd already write.** A *sorted*
precondition (every element ≤ its successor) lets the checker conclude adjacent elements
are ordered. The quantifier is plain GDK Groovy, so the runtime contract evaluates it too:

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

**Putting it together — a verified sort.** A recursive insertion sort whose result is
*proven sorted*: `insert` places `a[i]` into the sorted prefix (a store, by induction on
`i`), and `sort` composes it (by induction on `n`, relying on the `@Ensures` of the
`sort(a, n-1)` call right before `insert`). No loops — the recursion *is* the proof.

```groovy
@Requires({ 0 <= i && i < a.length && (0..<i - 1).every { a[it] <= a[it + 1] } })
@Ensures({ (0..<i).every { a[it] <= a[it + 1] } })
@Decreases({ i })
static void insert(int[] a, int i) {
    if (i > 0 && a[i] < a[i - 1]) {
        int t = a[i]; a[i] = a[i - 1]; a[i - 1] = t
        insert(a, i - 1)
    }
}

@Requires({ 0 <= n && n <= a.length })
@Ensures({ (0..<n - 1).every { a[it] <= a[it + 1] } })
@Decreases({ n })
static void sort(int[] a, int n) {
    if (n > 1) { sort(a, n - 1); insert(a, n - 1) }
}
```

This proves *sortedness* — the elements come out in order. It does **not** yet prove
*permutation* (that the output is a rearrangement of the input), which needs a multiset
model and `old(a)`; so a "sort" that zeroed the array would still pass here. Sortedness is
the harder-looking half and the part the order-reasoning machinery (quantifiers + induction)
makes reachable; permutation is tracked in the roadmap.

**Object state — instance fields, read and written.** Not just static functions: a method may
read and update its receiver's fields, and the checker threads field state across the write (so
the contract's entry `count` and exit `count` are different values, related by the assignment).
A mutator is proven to maintain its bound:

```groovy
class Counter {
    int count, max
    @Requires({ count < max })
    @Ensures({ count <= max })
    void increment() { count = count + 1 }
}
```

A postcondition can relate the *exit* state to the *entry* state with `old` — `@Ensures({ count
== old.count + 1 })` — and `old` reaches into array contents too, which is how a method frames what
it leaves alone: a setter that touches only `a[j]` proves every other element is unchanged,
`@Ensures({ (0..<a.length).every { it == j || a[it] == old.a[it] } })` (groovy-contracts clones the
field for `old`, so this holds at runtime as well as in the proof).

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

## Building & testing

Requires JDK 25. It builds against `org.apache.groovy:6.0.0-SNAPSHOT` from the
[ASF snapshot repository](https://repository.apache.org/content/repositories/snapshots) —
it relies on some fixes due for release in the next Groovy 6 pre-release.

```sh
./gradlew verify          # compile a battery of good/bad snippets and assert diagnostics
VERIFY_VERBOSE=1 ./gradlew verify   # also print the counterexamples for refuted cases
```

The self-test ([`src/test/groovy/VerifyHarness.groovy`](src/test/groovy/VerifyHarness.groovy))
compiles annotated snippets on the fly and asserts that good ones verify and
bad ones fail with the expected diagnostic.

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

- integer `+`, `-`, and *linear* `*` — a product needs a constant operand, but any
  closed constant subterm is folded first, so `(2 + 2) * (2 + 2)` and `a[(1 + 1) * 2]`
  are fine; `/` and `%` are checked for divide-by-zero but not otherwise modelled;
- comparisons, the boolean connectives `&&`/`||`/`!`, and the conditional `?:` — all
  short-circuit-aware, so a guard's left operand protects accesses in its right
  (`i > 0 && a[i - 1] < a[i]`) and a `?:` branch is checked under its condition;
- the size / nullity / membership oracles from the table above
  (`xs.size()`, `x == null`, `xs.contains(y)`, `x.equals(y)`, `isEmpty()`);
- array/list contents under Z3's array theory (`a[i]` reads, `a[i] = v` updates) with
  bounded-universal quantifiers — `Forall.range` or the native GDK idioms
  `(lo..<hi).every{…}` / `xs.indices.every{…}` / `xs.every{ it… }`;
- fuel-bounded inlining of contract-free pure functions (a closed call like
  `pow2(10)` is evaluated to a literal, a symbolic one unfolded);
- scalar instance-field reads (`this.count` / bare `count`) in contracts and bodies.

For method bodies: straight-line code, `if`/`else`, locals and instance fields (re-assignable,
tracked in SSA so a mutator's pre/post state differ), and a single annotated `while` loop. See
`Encoder` and the roadmap for the exact boundaries.

## Architecture

| File | Role |
|---|---|
| `VerifyChecker` | the `@TypeChecked` extension; call-site, body, loop & implicit checks |
| `Encoder` | Groovy expression → SMT (the fragment lives here) |
| `BodyEncoder` / `LoopEncoder` | path enumeration & symbolic execution for `@Ensures`/loops |
| `PathFacts` | enclosing-`if` path conditions per expression site |
| `ContractExpansionTransform` | captures verbatim contract text + clean body snapshots at CONVERSION |
| `SmtBackend` / `Z3Backend` | the solver seam and its z3-turnkey implementation |
| `Reporter` | OpenJML-style diagnostics with inline counterexamples |

`Encoder` is written against the `SmtSession` interface; `Z3Backend` is the only
concrete binding, so an alternative solver is a drop-in.

## License

Apache-2.0.
