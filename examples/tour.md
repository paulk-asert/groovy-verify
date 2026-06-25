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

# The five-act tour

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

## Act 1 — What a proof looks like

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

**The closure-style iterations too: `.each` and `.eachWithIndex`.** `xs.each { x -> … }` — and the implicit
`xs.each { … it … }` — model as that *same* for-in, but **safety-only**: the auto bounds invariant proves
per-element properties and bounded reads with no hand-written `@Invariant`, which a `.each` statement can't carry
anyway (a statement-level `@Invariant` on a method call is a Groovy parse error). So an *accumulating* `.each`
stays an honest loud-skip — reach for `for`/`while` there. `xs.eachWithIndex { x, i -> … }` adds the index as a
first-class, **user-named** loop variable, so `x` binds to `xs[i]` and `i` reads in contracts and counterexamples
exactly as you wrote it:

<!-- doclint:case p161-each/i-eachwithindex-element-index-property-verifies -->
```groovy
@Requires({ a != null && (0..<a.length).every { a[it] >= 0 } })
static void f(int[] a) {
    a.eachWithIndex { int x, int i -> assert x >= 0 && i >= 0 }
}
```

**Where `.each` stops, a loop invariant begins — the edge of internal iteration.** The per-element auto-invariant
that makes `.each` free for safety is also its ceiling. The moment a loop *accumulates* a result, the postcondition
needs an inductive `@Invariant` relating the accumulator to the iteration — and a `.each` statement has nowhere to
hang one (a statement-level annotation on a method call won't parse). A `for` / `while` / for-in *does*: its index is
a real, in-scope variable, and the loop can carry `@Invariant` / `@Decreases` — the **extra information that internal
iteration trades away**. So `a.each { c += 1 }` trying to prove `result == a.length` loud-skips, while the *identical*
accumulation written as a `for` proves it outright:

<!-- doclint:case p161-each/d2-same-accumulation-proven-as-a-for-loop -->
```groovy
@Ensures({ result == a.length })
static int count(int[] a) {
    int c = 0
    @Invariant({ c == i && i <= a.length })
    @Decreases({ a.length - i })
    for (int i = 0; i < a.length; i++) { c += 1 }
    c
}
```

The `@Invariant` frames the accumulator — `c` tracks the index — so establishment (`c == i` at `i = 0`), preservation
(`c+1 == i+1`), and use (`i == a.length` at exit, hence `c == a.length`) discharge the postcondition, and `@Decreases`
adds termination; flip the spec to `a.length + 1` and it refutes with `count(new int[0])`. The rule of thumb:
**reach for internal iteration (`.each`) for per-element safety; reach for a loop with an `@Invariant` the moment you
need to prove what the loop *computes*.**

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

## Act 2 — Bugs the compiler now catches

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
`VERIFY_SUGGEST`, `VERIFY_EXPLAIN`), each leaving the default path untouched; they're collected in
[TOOLING.md](../TOOLING.md).

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

**Not a toy — this is [Joshua Bloch's binary-search bug](https://research.google/blog/extra-extra-read-all-about-it-nearly-all-binary-searches-and-mergesorts-are-broken/).**
For nine years `java.util.Arrays.binarySearch` — and every mergesort written the same way — computed its
midpoint as `(low + high) / 2`, which overflows once the array is large enough that `low + high` exceeds
`Integer.MAX_VALUE`, returning a *negative* index. Bloch noted the bug "probably would have been caught by
formal verification." Here it is, caught at compile time (Groovy's `.intdiv(2)` is Java's integer `/`; the
overflow is in the `low + high` addition, before any division):

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

The counterexample *is* the failing scenario: a midpoint near the top of a two-billion-element array. Bloch's
one-line fix verifies — `low + (high - low) / 2` stays within `[low, high] ⊆ [0, Integer.MAX_VALUE]`, so no
addition can overflow:

<!-- doclint:case p-bloch-binsearch/fixed-midpoint-low-high-low-intdiv-2-verifies -->
```groovy
@CheckOverflow
@Requires({ 0 <= low && low <= high })
@Ensures({ low <= result && result <= high })
static int mid(int low, int high) { low + (high - low).intdiv(2) }
```

The same machinery catches the **`Math.abs(Integer.MIN_VALUE)` gotcha**. The JDK's `Math.abs(int)` is
`n < 0 ? -n : n`, and `-Integer.MIN_VALUE` overflows — there is no `+2³¹` in a signed `int` — so
`Math.abs(Integer.MIN_VALUE)` is *itself* `Integer.MIN_VALUE`, a negative result. The natural claim "absolute
value is non-negative" therefore refutes, at exactly that one input:

<!-- doclint:case p-abs-minvalue/abs-claims-non-negative-but-overflows-at-min-value -->
```groovy
@CheckOverflow
@Ensures({ result >= 0 })          // "the absolute value is non-negative" — false at MIN_VALUE
static int abs(int n) { n < 0 ? -n : n }
```

```
Possible ArithmeticException: negation overflows 32-bit signed range
    obligation: Integer.MIN_VALUE <= -n && -n <= Integer.MAX_VALUE
    counterexample: n = -2147483648
    fails on: abs(-2147483648)
```

Excluding the single offending input — `@Requires({ n > Integer.MIN_VALUE })`, which is the honest precondition
`Math.abs` carries in its own Javadoc — verifies.

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

## Act 3 — Whatever your data is

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
**evaluation order** — the JLS's left-to-right rule evaluates the LHS index before the right-hand side, so the
`i` in `dst[i]` reads the *old* value just as the hoisted-after `i++` does. What it refuses is a variable read
*after* its own increment — `x = i++ + i`, where the second `i` is the new value — which skips loudly rather
than risk mis-modeling.

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
And the *element* itself is nullity-checked: calling a method on `xs[i]` (or `xs.get(i)`) raises
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
neither side is a constant) is handled by Z3's non-linear integer arithmetic (NIA), so sign facts
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
*`BigDecimal`* division (`5 / 2 == 2.5G`), modelled with Z3's exact-real arithmetic so a spec
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

## Act 4 — Change, tracked soundly

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
its entry-snapshot machinery, so the proof and the runtime check agree. A wrong relation (`result.a ==
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

## Act 5 — All the way to a real algorithm

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
@Ensures({ result == a[0..<n * m].sum(0) })
static int matrixSum(int n, int m, int[] a) {
    int sum = 0, i = 0, k = 0
    @Invariant({ 0 <= i && i <= n && k == i * m && sum == a[0..<k].sum(0) })
    @Decreases({ n - i })
    while (i < n) {
        int j = 0
        @Invariant({ 0 <= i && i < n && 0 <= j && j <= m && k == i * m + j && sum == a[0..<k].sum(0) })
        @Decreases({ m - j })
        while (j < m) { sum += a[k]; k += 1; j += 1 }
        i += 1
    }
    sum
}
```

The running `sum == a[0..<k].sum(0)` extends one element per inner step (the `sum$` base/step axioms; the `0`
seeds the fold so the empty case is `[].sum(0) == 0` rather than Groovy's duck-typed `[].sum() == null`), the
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
> the tool applied to everyday problems, skip ahead to the [HumanEval Examples](humaneval.md).*

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


## More worked examples by domain

Beyond the five acts, more worked-and-verified examples by domain:

- **[HumanEval](humaneval.md)** — an external benchmark (Verus' suite) of LeetCode-shape problems we didn't pick.
- **[Dafny ports](dafny.md)** — the Dafny community's own credentials: `SumMax` (VSComp'10), `Find`, `BinarySearch`.
- **[OpenJML ports](openjml.md)** — `Max by elimination` and `ChangeCase`, from the JVM's closest prior art (CC BY-NC).
- **[Concurrency](concurrency.md)** — the *local* half of locks, agents, dataflow, channels, and rely/guarantee; the *structural* half (Lincheck / TLA+ TLC / Fray) is the [three rungs](../CONCURRENCY.md).
- **[Units of measurement](units.md)** — the Mars-orbiter bug, three ways: JSR 385 dimensions (the unchecked `as Quantity<K>` cast), JSR 385 value/scale, and a bespoke `record` units type with verified `+`.
- **[Bean Validation](validation.md)** — `jakarta.validation` / `javax.validation` constraints (`@Positive`, `@Min` / `@Max`, `@Size`, `@NotEmpty`) read as compile-time preconditions, discharged for free from annotations you already wrote.
- **[Miscellaneous](miscellaneous.md)** — ring buffer, Duplets, FizzBuzz, a string-concat law, a type hierarchy (inheritance / traits / Liskov), inline `assert` lemmas, and invariant inference.
- **[Thread-local IFC (Smith)](smith.md)** — Graeme Smith's Dafny approach: information flow (a security lattice + noninterference) and rely/guarantee, combined in the §VII capstone.

---

Back to the [README](../README.md).
