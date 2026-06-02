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

# Roadmap

`groovy-verify` proves a point: an SMT-backed type-checking extension can
produce Dafny-shaped verification diagnostics for Groovy today, with no
language change. Explicit contracts (`@Requires`, `@Ensures`, `@Invariant`,
`@Decreases`) and the implicit preconditions every program carries (array
bounds, division, null) are discharged by Z3 at the caller's compile time,
before any runtime check would fire. This document records what is in place and
where it goes next.

Each item slots in as new encoder cases, new verification-condition sites, or
new annotation kinds, without restructuring the engine. The ordering is by
value-to-cost — how much a capability is worth to someone writing real Groovy,
against how much work and solver risk it adds. The increments are not strictly
dependent on each other, but the later ones assume the encoder fragment of the
earlier ones.

Verification is sound *within* a deliberately small fragment and **loudly
unsound outside it**: anything the encoder cannot model emits a "skipped"
diagnostic rather than passing silently. That honesty is a design choice, not a
limitation to be apologised for — see [Non-goals](#non-goals).

---

## Phase 1 — Safety: array bounds, division by zero, null  *(shipped)*

**The "every developer recognises this" win.** No annotation surface; these are
*implicit preconditions* that fire automatically on indexing, division, and
dereference. OpenJML splits them into `UndefinedNegativeIndex`,
`UndefinedTooLargeIndex`, `UndefinedZeroDivision`, `UndefinedNullDeReference`;
the same taxonomy applies here.

**How it works (shipped):**

- `VerifyChecker.verifyImplicitObligations` runs in `afterVisitMethod` for every
  method in the annotated scope. It walks the *clean body snapshot*
  `ContractExpansionTransform` takes at CONVERSION — not `method.getCode()` —
  so groovy-contracts' injected runtime asserts are never mistaken for the
  author's dereferences. (The snapshot is now taken for every method, not just
  `@Ensures`/loop ones.)
- An `ObligationCollector` (a `ClassCodeVisitorSupport`) gathers three site
  kinds: array/list **subscripts** (`a[i]`), **division/modulo** (`a / b`,
  `a % b`), and instance-method **dereferences** on a named parameter/local
  receiver. Static calls, `this`, and calls on non-variable receivers are
  skipped — they are provably non-null or out of reach.
- Each site is discharged by the same machinery as a call-site precondition:
  assume the method's own `@Requires` and the enclosing path facts, assert the
  *negation* of the obligation, and ask Z3 whether that is satisfiable. A model
  is a counterexample.
  - index `a[i]` → `0 <= i && i < a.size`
  - division `a / b` / `a % b` → `b != 0`
  - dereference `r.m(...)` → `r != null`
- A **size oracle** mints an integer constant `<recv>.size >= 0` on demand; a
  **nullity oracle** mints a boolean per reference. The size constant is shared
  with the `.length`/`.size()` contract syntax of [Phase 4](#phase-4--richer-fragment-in-requiresensures-shipped),
  so a contract that bounds a collection's size and an indexing check inside the
  body agree on the same symbol.

**Diagnostic:**

```
Cannot prove array index in bounds at this access
    obligation: 0 <= i && i < a.size
    counterexample: a.size = 0, i = -1
```

```groovy
@TypeChecked(extensions = 'verification.VerifyChecker')
class Demo {
    static int at(int[] a, int i) {
        if (i >= 0 && i < a.length) return a[i]   // verified
        return -1
    }
    static int bad(int[] a, int i) {
        a[i]                                       // REFUTED: i may be < 0 or >= a.size
    }
}
```

**Known limit.** The implicit checks are path-sensitive (they honour enclosing
`if`s) but not value-flow-sensitive: they do not track local assignments, so the
discharging examples are guard- or `@Requires`-based. Index reasoning that
depends on a loop counter (proving `a[i]` safe *after* a `while`) needs the loop
machinery of Phase 3 fused with the bounds obligation, and is not yet wired
through. Counterexamples report integer values; nullity is boolean, so a
null-dereference refutation names the obligation but not a concrete value.

---

## Phase 2 — Postconditions: `@Ensures`  *(shipped)*

**The "now we're verifying methods produce the right answer" win.** The first
capability that requires symbolic execution of the method body, not just the
call site — the checker becomes *per-method*, not only *per-call*.

**How it works:**

- No new annotation. Stock `@groovy.contracts.Ensures({ ...result... })`;
  groovy-contracts generates the runtime postcondition check (including on
  *static* methods) and owns the `result`/`old` names, so the type checker never
  trips over them.
- `ContractExpansionTransform` — a global transform at CONVERSION — reads the
  contract closure while it is still a `ClosureExpression`, captures its verbatim
  text with power-assert's `SourceText`, and stashes it on a RUNTIME
  `@ContractSource`. `VerifyChecker` reads that back and re-parses it — the
  built-in annotation itself retains only a `Class` reference to a generated
  closure, so the source would otherwise be gone by compile time.
- `BodyEncoder` enumerates the body's straight-line execution paths (forking at
  each `if`, threading a per-path step list, so no join-point merge is ever
  needed). For each path it emits the VC
  `path_condition ∧ ¬(postcondition[result ↦ returned_expr])` and discharges it.

**One non-obvious interaction.** groovy-contracts rewrites the method body *in
place* at INSTRUCTION_SELECTION — prepending an `old` map, wrapping in
try/catch, appending the postcondition assert — before the type-checking
extension runs. So the verifier must analyse the **clean CONVERSION snapshot**,
not `method.getCode()`.

```groovy
@Ensures({ result >= a && result >= b })
static int max(int a, int b) { if (a > b) a else b }       // verified

@Ensures({ result >= a && result >= b })
static int maxBuggy(int a, int b) { if (a > b) b else a }  // REFUTED: a=1, b=0
```

The encoder's scope is straight-line + if/else + single return. Symbolic
execution grows tendrils (`break`/`continue`/mid-method `return`, exceptions,
finally blocks), so everything else is a "skipped postcondition" diagnostic.

---

## Phase 3 — Loops: `@Invariant` + `@Decreases`  *(shipped)*

**The classical inductive proof.** Three obligations per loop, plus a fourth for
termination:

1. **Establishment** — invariant holds on first entry.
2. **Preservation** — invariant ∧ guard ∧ one body iteration ⇒ invariant still holds.
3. **Use** — invariant ∧ ¬guard ⇒ whatever VC fires after the loop (e.g. the postcondition).
4. **Progress** (`@Decreases`) — invariant ∧ guard ∧ body ⇒ the measure strictly decreases and stays ≥ 0.

**How it works:**

- No new annotation. groovy-contracts already ships
  `@groovy.contracts.Invariant`/`@groovy.contracts.Decreases` *on loop
  statements*; its transforms inject the runtime checks. We capture their text
  the same way as `@Requires`/`@Ensures` and leave the closures intact.
- `LoopEncoder` does havoc-and-assume symbolic execution: a fresh `Encoder` per
  verification condition gives havoc-by-default (any name a context never binds
  is an unconstrained fresh value), an assignment is a re-bind (so SSA renaming
  falls out for free), and the invariant is assumed, the body executed once, and
  the invariant re-asserted.
- A *deeper* CONVERSION snapshot preserves the loop subtree — guard, clean body,
  and the intact `@Invariant`/`@Decreases` closures — because groovy-contracts
  mutates the loop's *inner* body in place.

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

All four VCs discharge clean; mutate an increment or the invariant and the
diagnostic names exactly which obligation fails. **Caveat:** the havoc set is
currently *every* in-scope variable rather than the loop's live-modified set —
sound but loose, so non-trivial loops will draw more "could not decide" answers
than a tighter modified-set analysis would. Loop contracts are never read across
a module boundary, so the rebuild discipline below does not apply to them.

---

## Phase 4 — Richer fragment in `@Requires`/`@Ensures`  *(shipped)*

**The extensions that unlock most contracts people actually want to write.**
Each is a small `Encoder` addition; the work was choosing the right encoding.

- **`xs.size()` / `xs.length`** for `List`/`String`/arrays — the size oracle from
  Phase 1, now exposed in contract syntax and sharing its `<recv>.size` constant.
- **`xs.isEmpty()`** as sugar for `xs.size() == 0`.
- **`x == null` / `x != null`** — first-class nullity via the nullity oracle,
  detected at the comparison so `null` need not itself be a fragment value.
- **`x.equals(y)`** for numeric types — the method form of `x == y`.
- **`xs.contains(y)`** — modelled as an *uninterpreted predicate*
  `contains$xs : Int -> Bool`. Sound, and `contains(y)` assumed entails
  `contains(y)` proved, but with no membership reasoning until the quantifier
  axioms of [Phase 5](#phase-5--quantifiers). It deliberately stops short of the
  trigger cliff.

The seam grew two methods — `SmtBackend.boolVar` (nullity) and
`uninterpretedPred` (contains) — both implemented once in `Z3Backend`.

**Cross-boundary oracles (shipped).** Inside a unit these all work: a method's
own `@Requires({ s != null })` is assumed when checking its body, and an
`@Ensures` referring to `xs.size()` is checked against the body. At a *call* site
the formal↔actual binding now ties the **size and nullity oracles** as well as
the integer value: when the actual is a named reference and the callee's contract
references its size or nullity, the formal's oracle is asserted equal to the
actual's. Two changes make this land cleanly:

- The oracle is tied **only when the contract actually mints it** on the formal
  (`Encoder.hasSizeOracle`/`hasNullityOracle`), so a purely-nullity precondition
  doesn't fabricate an `xs.size` term in the counterexample.
- A call site now also **assumes the enclosing method's own `@Requires`**, mirror-
  ing what the implicit-obligation checks already did via `assumeContext`. A
  precondition is a given throughout the body, so a method declared
  `@Requires({ s != null }) m(String s) { callee(s) }` can discharge `callee`'s
  `@Requires({ x != null })` from its own contract — not only from an `if`-guard.

So a caller proving a callee's `@Requires({ x != null })` or
`@Requires({ xs.size() > 0 })` across the boundary now verifies, from either a
guard or the caller's own contract. **Residual cosmetic limit:** a refuted
reference-typed call site still lists the formal's meaningless integer shadow
(`s = 0`) alongside the meaningful oracle value — the integer constant minted for
every formal so numeric counterexamples read `x = -1`. Type-aware counterexample
filtering would suppress it; small, not yet wired.

---

## Phase 5 — Quantifiers

**The frontier.** Necessary for binary-search correctness, two-sum, sortedness
invariants, "every element of this array satisfies P". Z3 handles bounded
universals well if the patterns are set up right; unbounded quantifiers are
where the trigger cliff lives.

**Scope strictly to bounded universals.** Syntax for the user:

```groovy
@Requires({ Forall.range(0, arr.length, { i -> arr[i] >= 0 }) })
```

…where `Forall.range(lo, hi, predicate)` is a static helper the encoder
recognises and rewrites to a Z3 `mkForall` over an integer variable constrained
`lo <= i < hi`. The closure body is the matrix; `arr[i]` becomes `(select arr i)`
under Z3's array theory.

**Risks specific to this phase:**

- Z3 returns UNKNOWN on quantified formulas it can't pattern-match. Triggers are
  the cliff. Mitigation: limit to the `∀ i: lo <= i < hi` shape, ensure every
  quantified occurrence of `arr[i]` is a valid trigger, set a generous timeout.
- Encoding arrays via Z3's array theory changes the whole VC shape. Plain
  indexing becomes `(select arr i)`; `arr.size` becomes an uninterpreted
  function constrained appropriately. This also retires the "array contents not
  modelled" limit that Phase 1 lives with today.
- Existentials are harder than universals; defer.

Estimated work: a couple of weeks, with a real chance part of it is spent
fighting trigger heuristics. Risk: high. Target: the bounds-and-sortedness proof
for binary search, with sortedness as
`Forall.range(0, arr.length - 1, { i -> arr[i] <= arr[i+1] })`.

---

## Phase 6 — Optional heavy lifts

If the project grew into something widely used, these would be on the table.
All expensive, none strictly necessary to make the verification story
persuasive.

- **Full NIA.** Lift the encoder's restriction that multiplication requires at
  least one literal operand. Z3's `qfnia` tactic handles a lot of practical NIA
  but is incomplete; would need timeout discipline and possibly per-VC tactic
  selection.
- **Bounded integer modelling.** Catch overflow as a verification failure rather
  than silently working modulo 2³². Encode ints as fixed-width bitvectors; every
  arithmetic VC gains a range side-condition. Cost: ~2× solver time, much more
  expressive errors.
- **Bitwise / shift operators.** The same bitvector encoding picks these up for
  free.
- **Inter-procedural reasoning.** Use a callee's `@Ensures` as facts when
  reasoning about the caller (currently only its `@Requires` is used). Small to
  add, but transitively requires callees be re-verified when their contracts
  tighten — a real build-time cost. The cross-boundary oracle binding it builds
  on is now in place (Phase 4), so this is unblocked.
- **Heap/aliasing.** Don't. Groovy makes this very hard and the payoff is small
  for the fragment most developers care about.

---

## Non-goals

Things deliberately not pursued, because they don't pay back:

- **Soundness as a hard property.** This is *loud unsoundness*: everything
  outside the fragment emits a "skipped: outside fragment" diagnostic, which is
  honest. Chasing actual soundness would mean rejecting any program that touches
  anything outside the fragment — which is most of them.
- **Concurrency.** No race detection, no dataflow reasoning. A different tool.
- **Floating point.** SMT handles FP but slowly and with surprising results. If
  the project ever targets numeric code, revisit.
- **Generated proof certificates.** Out of scope.
- **IDE squiggles.** Diagnostics go through `addStaticTypeError`, which IDEs
  surface via their Gradle integration. Going further — inline counterexample
  popups, fix suggestions — is downstream of this work, not part of it.

---

## Cross-cutting risks worth noting up front

- **Compilation slowdown.** Z3 calls take 10–100 ms each. A large module with
  hundreds of annotated call sites and implicit-check sites could add noticeable
  seconds to a compile. Mitigations: cache VCs by `(signature, path-condition
  hash)` so unchanged sites reuse prior results; run the checker only in a
  "verify" configuration (a separate source set or a `-PverifyEnabled=true`
  flag).
- **`@CompileStatic` incompatibility.** The checker is a type-checking
  extension; code authored under `@CompileStatic` needs the checker to either
  work as an AST transformation instead, or run before `@CompileStatic` makes
  its static decisions. Substantial design work; deferred.
- **Producer/consumer rebuild discipline.** The contracts are stock
  `groovy.contracts` annotations; the only thing this library adds at
  producer-compile-time is the `@ContractSource` that captures verbatim contract
  text into bytecode. That carrier matters in exactly one situation: a consumer
  statically verifying a *call* to a `@Requires`-annotated method in **another
  module**. For that to work, the producer must have been compiled with
  `groovy-verify` on its classpath; otherwise those call sites degrade to
  "skipped". This does **not** apply to `@Ensures`/`@Invariant`/`@Decreases` or
  the implicit checks — they are verified in-unit, where the checker is already
  running. And groovy-contracts' *runtime* checks are orthogonal: a producer
  built without this library still enforces its contracts at runtime; it merely
  forgoes the consumer-side compile-time proof.
- **Z3 model expressiveness.** Counterexamples show concrete integer values,
  which is great for `isqrt(-1)`. Once arrays are in scope (Phase 5), showing
  "the array such that ¬P holds" gets visually awkward — Z3's array models look
  like `(store (store (as-array k!0) 0 -1) 1 0)`. A pretty-printer for array
  models is small but worth budgeting.

---

## Definition of done, per increment

An increment is done when:

1. The motivating example compiles cleanly under the checker.
2. *Some* deliberately-broken mutation of it fails to compile, with a diagnostic
   that points at the right source location and includes a counterexample with
   the right values.
3. *Another* mutation that is incompletely specified produces a "could not
   decide", not a silent pass.
4. The README's capability table grows by N rows, and the self-test harness
   (`./gradlew verify`) gains good/bad cases for it.
5. Solver wall-clock per site stays under ~200 ms on a current laptop.

Anything else — broader coverage, more examples, better messages — is polish
that does not gate the next increment.

---

## A note on ordering

The temptation is to do Phase 5 (quantifiers) early because the binary-search
example is so striking. The drop-off from "works on the example" to "works on
the next thing someone tries" is steepest there, so the foundation came first:
Phases 1 → 2 → 3 → 4, each catching a class of bug developers viscerally
recognise, none leaning on quantifier heuristics. With that in place, Phase 5
can begin — but as its own multi-week effort, not a quick win bolted onto a
demo.
