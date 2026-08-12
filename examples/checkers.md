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

# Relationship to Groovy's other checkers

groovy-verify is one of a family of `@TypeChecked` extensions, and it deliberately owns a narrow,
deep slice — SMT-backed *functional* verification. A few relationships place it: how its null story
relates to Groovy's existing null tooling, how it composes with the sibling regex and purity checkers
(orthogonally, and cooperatively), and what guards the code its fragment can't yet reach.

## Null handling — three layers, one of them a sibling

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
`@Nullable` awareness, does not model `?.`, and — beyond the `@NonNull` forms it reads as contracts
and suppressions (returns, fields, per-element; below) — makes every named-receiver dereference *and*
every indexed-element dereference (`xs[i].method()` / `xs.get(i).method()`, Phase 37) an unconditional
obligation against per-element nullity oracles.
**For dedicated null-safety, reach for `NullChecker`;** the `@Nullable` direction — deliberately a
no-op here, where an unannotated element already obligates — is exactly what its annotations express:
since Groovy 6.0.0-beta-2 (GROOVY-12252) it acts on `@Nullable` type arguments reaching results
through generics (`get(0)`, `xs[0]`, `head()`).

Because both are just extensions, they **compose** — nullness-by-annotation and SMT functional
verification in a single compile, each doing what it is best at. And there's a clean seam where
groovy-verify proves a condition NullChecker can only *assume*. NullChecker's element story is
annotation-driven — since 6.0.0-beta-2 (GROOVY-12252) a declared `List<@Nullable String>` makes
`get(0)` / `xs[0]` / `head()` nullable — but an *unannotated* element type, even in flow-sensitive
`strict` mode, it silently assumes non-null. groovy-verify makes that dereference an
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
model having no handle on the element. The annotation-driven direction **composes** too. A `@NonNull`
return is read as an implicit `result != null` postcondition groovy-verify **proves** at the value level —
catching a nullable value that reaches the return through reasoning (arithmetic, contracts, a `@Requires`-only
guarantee) NullChecker's flow model passes over. A `@NonNull` *field* becomes an implicit object invariant
`field != null` that groovy-verify proves *establishment and preservation* for — every constructor leaves it
non-null, no method nulls it. NullChecker enforces the syntactic half of that story (a literal `null` store
is flagged, and since 6.0.0-beta-2 `strict` mode flags a never-assigned `@NonNull` field — GROOVY-12251);
the *value*-level half stays groovy-verify's: whether what a constructor or method actually assigns is
provably non-null under its own `@Requires`. The two don't
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
groovy-verify refutes the implicit invariant with `<init>(null)` while NullChecker stays silent, even with
6.0.0-beta-2's definite-initialization check (GROOVY-12251): the field *is* assigned — it is the assigned
*value* whose non-nullness has lost its warrant, a value-level question only the prover asks. Add a
`void clear() { name = null }` and both speak, each from its own end: NullChecker flags the literal store
(`Cannot assign null to @NonNull variable 'name'`), groovy-verify refutes invariant *preservation* at
`clear` — and would still do so if the null arrived by flow (`void clear(String s) { name = s }`) where
the literal-store check has nothing to see. The design-by-contract lifecycle framing is groovy-verify's
to supply.

## Two checkers, one regex — syntax beside semantics

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

## `CombinerChecker` — shape beside semantics

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
their own javadoc says *"this annotation asserts the laws; it [checks nothing]"*. groovy-verify reads the
annotation directly: for any `@Associative`/`@Reducer` combiner with an equational `@Ensures({ result == E })`, it
synthesises and discharges the very laws the annotation claims — associativity for both, plus identity over the
declared `zero` for `@Reducer`. So the hand-written `associative` lemma above is **redundant**; delete it and the
proof still holds, because `@Reducer(zero = '0')` already obliges it:

<!-- doclint:ignore README illustration: Sum monoid (@Reducer auto-proves) -->
```groovy
@TypeChecked(extensions = ['groovy.typecheckers.CombinerChecker', 'verification.VerifyChecker'])
class Sum {
    @Reducer(zero = '0')                              // asserts a monoid — and groovy-verify *proves* it:
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

A bad annotation fails loudly: `@Associative` on subtraction refutes with `Cannot prove @Reducer
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

## `MonadicChecker` — laws beside shape

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
    @Pure static Maybe some(Object v) { new Maybe(true, v) }   // unit
    @Pure static Maybe none()         { new Maybe(false, null) }

    @Requires({ f != null }) Maybe flatMap(Function f) { present ? (Maybe) f.apply(value) : this }
    @Requires({ g != null }) Maybe map(Function g)     { present ? some(g.apply(value)) : this }   // Vavr-style

    static Maybe addPair() { DO(a in some(2), b in some(3)) { some(((Integer) a) + ((Integer) b)) } }
}
```

Each extension does a *distinct* job on the one class: **MonadicChecker** shape-checks the `DO` comprehension,
**PurityChecker** the side-effect freedom of the `@Pure`-marked `some` / `none` the laws build on (it checks
the methods you mark — `flatMap` / `map` call an arbitrary `Function`, so they can't be `@Pure`), **NullChecker**
the nullness, and **groovy-verify** proves the five laws from `@Monadic` alone — all four compile quietly because
this `Maybe` *is* lawful.

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

## `PurityChecker` — discharging a premise groovy-verify relies on

Composition isn't always orthogonal. groovy-verify's pure-function evaluation (Phase 8a) proves a method
by *inlining a contract-free same-class helper as a value* — sound only if that helper is referentially
transparent, which groovy-verify **assumes but never checks**. `PurityChecker` verifies precisely that,
turning the unstated premise into a machine-checked one:

<!-- doclint:case p-multichecker/puritychecker-verifychecker-pure-helper-contract-proven-via-pure-eval -->
```groovy
@TypeChecked(extensions = ['groovy.typecheckers.PurityChecker', 'verification.VerifyChecker'])
class C {
    @Pure
    static int triple(int n) { 3 * n }            // PurityChecker: provably side-effect-free
    @Ensures({ result == 30 })
    static int f() { triple(10) }                 // groovy-verify: proven by evaluating triple(10)
}
```

Both pass — and `f`'s proof rests on *checked* purity, not trusted purity. Give `triple` a side
effect (`counter += 1`) and `PurityChecker` names the exact violation (`@Pure violation: field
assignment to 'counter'`) where groovy-verify — unable to evaluate the impure body — would only shrug a
vague `Cannot prove`. This is the deepest of the pairings: one checker underwrites a premise the other
takes on faith.

## Outside the fragment, the code is still guarded

groovy-verify is *loudly* partial: anything outside its fragment is skipped, never silently passed
(see [Non-goals](../ROADMAP.md)). Two safety nets mean "skipped" does not mean "unprotected":

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


---

Back to the [README](../README.md).
