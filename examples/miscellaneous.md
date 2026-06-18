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

# Miscellaneous examples


Examples that don't belong to one of the per-source galleries: a verified mutable data structure, a
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

