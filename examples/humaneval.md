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

# HumanEval examples


The examples in the main README are ours — chosen to showcase the fragment. To check the engine against problems
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

Read against the five Acts of the [README](../README.md), the corpus re-runs the same machinery on problems we didn't pick —
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
the **SumMax** example in the [Dafny examples](dafny.md) below is a worked instance.
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

Three capabilities compose in one method: **prefix early-returns**
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

Task 071 (`triangle_area`) is a neat case of staying inside a decidable fragment by *reformulating*. The original
returns the triangle's area — Heron's `√(s·(s−a)·(s−b)·(s−c))` — or `-1` when the sides can't form a triangle. That
square root is irrational, out of reach for exact arithmetic; the Verus port sidesteps it by returning the
**squared** area, keeping everything in exact integers. groovy-verify then proves the spec the overflow-only
original omits — *a valid triangle's squared area is non-negative, an invalid one is `-1`*:

<!-- doclint:case he071-triangle-area/squared-area-is-non-negative-or-1 -->
```groovy
@Requires({ a >= 0 && b >= 0 && c >= 0 })
@Ensures({ result == -1 || result >= 0 })
static int triangleAreaSquared(int a, int b, int c) {
    if (a + b > c && a + c > b && b + c > a) {
        int s = (a + b + c).intdiv(2)
        return s * (s - a) * (s - b) * (s - c)
    }
    return -1
}
```

The proof leans entirely on the **validity guard**. The triangle inequality `b + c > a` forces the half-perimeter
`s = ⌊(a+b+c)/2⌋ ≥ a` (and `≥ b`, `≥ c`) — pure linear reasoning over floor division (`intdiv`) — so each of the
four factors `s`, `s−a`, `s−b`, `s−c` is non-negative, and so is their product (the same *product-of-non-negatives*
monotonicity lemmas that close the flat-matrix store bound). Drop two of the three inequalities and the guard no
longer protects the subtractions: `a=10, b=1, c=1` passes `a+b>c` alone yet gives `6·(−4)·5·5 = −600`, a negative
"area" — so the postcondition **refutes**, the bug an incomplete validity check hides.

And the overflow the Verus suite *does* check for is real here: turn on `@CheckOverflow` and even modestly-bounded
sides make the squared-area product **overflow** 32-bit `int`. The value property holds in exact arithmetic; the
machine-int width is a separate, genuine bug — both halves caught on the same six-line function.

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

