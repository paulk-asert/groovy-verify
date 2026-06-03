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

**Path-sensitivity, and the value-flow that followed.** The implicit checks are
path-sensitive (they honour enclosing `if`s). They were originally
*value-flow-blind* — local assignments were not tracked, and a bounds obligation
inside or after a loop was checked without the `@Invariant`. Both gaps are now
closed by [Phase 5](#phase-5--value-flow--loop-fused-safety-obligations-shipped),
which threads single-assignment locals and discharges loop obligations under the
invariant. Counterexamples report integer values; nullity is boolean, so a
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
  axioms of [Phase 6](#phase-6--quantifiers-shipped). It deliberately stops short of the
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

## Phase 5 — Value-flow & loop-fused safety obligations  *(shipped)*

**Completing Phase 1 — the everyday wins it used to miss.** The implicit safety
checks (array bounds, division, null) were path-sensitive but *value-flow-blind*:
each obligation was discharged in a fresh `Encoder` assuming only the method's
`@Requires` and the enclosing `if` facts, so every local was havoc-by-default and
the loop invariant was never in scope. Two recognisable patterns therefore failed
even though they are obviously safe:

- **(a) safety from an assignment, not a guard** — `int j = 3; a[j]` under
  `@Requires({ a.length > 5 })` was refuted, because `j = 3` was never threaded.
- **(b) the counted loop** — `while (i < n) { ... a[i] ... }` was refuted, because
  the bounds obligation at `a[i]` was checked without the loop's `@Invariant`.

Both now verify. The work stayed entirely inside the QF_LIA + oracle fragment —
no new theory, no quantifiers — the opposite of
[Phase 6](#phase-6--quantifiers-shipped)'s trigger cliff.

**How it works:**

- **5a — value-flow in straight-line / `if` bodies.** `verifyImplicitObligations`
  first tries a lenient walk of the body (`collectVfObligations`) that snapshots,
  for each obligation, the single-assignment bindings and `if`-guards in effect
  where it is *evaluated* — forking at each `if`, with the condition's own
  obligations evaluated before the branch. Each obligation is then discharged in
  a fresh session under `@Requires` + those reaching assignments (asserted as
  equalities) + those guards. Anything outside the fragment (a loop, a
  re-assignment, an unsupported statement) throws, and the original path-fact-only
  **havoc pass** runs as a sound fallback. *Guarded derived locals already
  verified before* — `if (j >= 0 && j < a.length) a[j]` works because the guard
  and the obligation share the same `j` handle — so 5a's marginal win is the
  *assignment-implied* facts.
- **5b — loop-fused bounds.** For a method whose body is an annotated loop, the
  obligations are discharged with the invariant in scope instead of via the havoc
  pass (`verifyLoopObligations`): prefix sites see `@Requires` + the straight-line
  prefix store; the guard and body sites additionally assume the invariant (and,
  in the body, the guard); suffix sites assume the invariant ∧ ¬guard. Each region
  is threaded with `LoopEncoder.symExec` (bind/SSA semantics — correct even when
  the counter is re-assigned). It **only** helps loops carrying an `@Invariant`
  strong enough to bound the index; otherwise it is an honest "could not decide".
- **Lenient `symExec`.** So that a body which *reads* the array (`s = s + a[i]`,
  outside the int fragment) does not abort the whole loop proof, an assignment
  with an unmodelable right-hand side now **havocs** its target (`Encoder.havoc`)
  rather than raising. Sound: havoc only ever makes the invariant/obligation VCs
  harder. This also retires a class of spurious "skipped loop" diagnostics.

```groovy
@Requires({ 0 <= n && n <= a.length })
static int sum(int[] a, int n) {
    int s = 0
    int i = 0
    @Invariant({ 0 <= i && i <= n })
    while (i < n) { s = s + a[i]; i = i + 1 }   // a[i] verified: i < n <= a.length
    return s
}
```

**Known limits.** Value-flow threading is single-assignment only — a
re-assignment throws the body out to the havoc fallback. Inside a loop body 5b
threads straight-line statements but does not fork on a nested `if`, so an
obligation guarded by an *inner* `if` is reasoned from the invariant alone, not
that guard (sound, less precise). And the per-site replay multiplies solver calls
— see the compilation-slowdown cross-cutting risk.

---

## Phase 6 — Quantifiers  *(shipped)*

**The frontier — bounded universals over arrays.** "Every element satisfies P",
sortedness, and the read/write reasoning that array algorithms need. Z3 handles
bounded universals well when the patterns are right; unbounded quantifiers are
where the trigger cliff lives, so the scope is **bounded universals only**
(existentials and unbounded quantifiers are deferred).

**Syntax for the user:**

```groovy
@Requires({ Forall.range(0, a.length) { a[it] >= 0 } })
```

`Forall.range(lo, hi, predicate)` is a static helper the encoder recognises and
rewrites to a Z3 `mkForall` over an integer constrained `lo <= i < hi`, with the
closure body as the matrix; `a[i]` becomes `(select a i)` under Z3's array theory,
and each such term becomes an instantiation trigger (one pattern per term, so a
matrix with several distinct selects — sortedness uses `a[i]` and `a[i+1]` —
instantiates robustly). The predicate is the trailing closure, naming the index
with `it` or an explicit `{ i -> ... }`; `Forall.range` stays executable, so the
groovy-contracts *runtime* check still works. It composes inside an ordinary
boolean `@Requires`/`@Ensures` (ANDed with normal conditions), reusing
groovy-contracts rather than a parallel annotation.

**Dependency note.** This natural `{ i -> ... }` spelling needs the patched local
`6.0.0-SNAPSHOT`: earlier groovy-contracts builds rejected *any* parameterised
closure (and `it`) nested inside a contract closure, which would have forced an
awkward static-marker workaround. The method-call surface is still the spike form
— [Phase 9](#phase-9--programmer-facing-surface-authoring--diagnostics) owns a
closer-to-idiom spelling.

**Read *and* write: `select` and `store`.** Reading covers proofs like binary
search. The write side models a single array's contents as a value — an immutable
Z3 array threaded through the method, each `a[i] = v` becoming `(store a i v)`
(`BodyEncoder` emits an `ArrayStore` step; a later read of `a[i]` sees the
update) — so a postcondition can describe the array a method *produced*: the
in-place-algorithm proofs (sort, partition, reverse) that are the Dafny-to-Java
showcase. This needs **no general heap or aliasing** (the non-goal below): it
assumes the array parameter is unaliased — the common case in algorithm code —
and reasons with value semantics. The `a.size` oracle and the `a` array value
share the source name, so a bounds obligation `i < a.size` and a `(select a i)`
agree; this retires Phase 1's "array contents not modelled" limit.

**In-loop `store` (shipped).** `store` is threaded through loop bodies too
(`LoopEncoder` rebinds `a := (store a i v)` on `a[i] = v`), so a quantified
`@Invariant` over the array's contents is preserved across the update — a
constant-fill (`a[i] = 0` ⇒ `Forall.range(0, n) { a[i] == 0 }`) verifies, and an
invariant the store breaks is refuted on preservation. Two surface notes the loop
case forced: inside `@Invariant` the quantifier must be written fully-qualified
(`verification.Forall.range(...)`) and with a typed index (`{ int j -> a[j] ... }`)
— groovy-contracts compiles the invariant closure for its runtime check, where
the import isn't in scope and `a[j]` needs an `int`. And loop invariants are now
captured *as text and re-parsed* (like `@Requires`/`@Ensures`), so the verifier
sees a clean CONVERSION AST rather than the live node later phases resolve to a
static call / `getAt`. **Still not done:** a full *in-place sort* — that needs the
sortedness-transitivity lemma, which is induction (Phase 7).

**Known limits.** Counterexamples for array/quantifier refutations show the
integer skeleton (`a.size`, indices) but not array contents or unconstrained
element values — honest, not yet concrete; the array-model pretty-printer
(cross-cutting risks) and the witness-as-failing-call idea (Phase 9) are the
follow-ups. UNKNOWN on a stalled quantifier stays a loud "could not decide"; the
user-supplied trigger/instantiation hint that would rescue it is the lightest
borrow from [Phase 8](#phase-8--beyond-smt-proof-by-computation-and-proof-hints).

---

## Phase 7 — Optional heavy lifts

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
- **Inter-procedural reasoning, and lemmas.** Use a callee's `@Ensures` as facts
  when reasoning about the caller (previously only its `@Requires` was used). The
  cross-boundary oracle binding it builds on is in place (Phase 4); the build-time
  cost is that callees must be re-verified when their contracts tighten. Its
  headline payoff is **lemmas** — the proof-structuring primitive Dafny users lean
  on most, and the one feature from Dafny's proof toolbox this fragment otherwise
  lacks. A lemma is just a `static` method with `@Requires`/`@Ensures` whose body
  the checker verifies and which a caller *invokes to inject its postcondition* as
  a fact; it lets a specify-and-prove developer scale past a single method's proof
  without a cross-compiler, and composes with the `assert … by`/`calc`
  decomposition of
  [Phase 8](#phase-8--beyond-smt-proof-by-computation-and-proof-hints)b.

  **Slice 1 — result-binding (shipped).** `int z = f(args)` now assumes `f`'s
  `@Ensures` with `result ↦ z` and formals ↦ actuals (`Encoder.translateWith` does
  the scoped substitution; the callee's `@Requires` is discharged separately at
  the call site). This is the *load-bearing* form: the caller cannot see inside
  `f`, so without the contract `z` is opaque (previously a "skipped
  postcondition"). Reasoning is modular — the callee's *contract* is used, never
  its body. Scope: same-class resolution by name + arity; self-calls excluded;
  `old` and array/frame effects unmodelled.

  **Slice 2 — induction (shipped).** A method may now assume *its own* `@Ensures`
  at a recursive call — the inductive hypothesis — gated on a method-level
  `@Decreases` measure whose well-foundedness is proved separately: at each
  recursive call `verifyTermination` discharges `0 <= measure[args] <
  measure[entry]` (substitution via `translateWith`, the decrease/≥0 shape from
  the loop progress check). So `sumUp(n)` with `@Ensures({ result >= n })` /
  `@Decreases({ n })` verifies by induction. The measure rides on the *same*
  stock `@Decreases` annotation groovy-contracts now accepts on methods
  (GROOVY-12060), so it is runtime-meaningful too — no verifier-only surface. If
  the measure can't be shown to decrease, or is outside the fragment, the
  inductive hypothesis is refused (loud, not silently accepted). Without
  `@Decreases`, a recursive call's result stays opaque → honest "skipped".

  **Slice 3 — standalone lemmas (shipped).** A lemma is a `void` method proved by
  induction and *called for its `@Ensures`*. Three pieces landed: `BodyEncoder`
  enumerates void methods (paths may fall through, no `result`); a standalone call
  statement becomes a `LemmaCall` step that assumes the callee's `@Ensures` (no
  result binding) — refused as outside-fragment if the call has no usable
  contract, so an unmodelled side-effecting call still "skips" rather than
  false-passes; and the self-IH + termination VC also fire on `LemmaCall`
  self-calls. This closes the Dafny loop: e.g. *sortedness transitivity*
  (`a[i] <= a[j]` for `i <= j` from adjacent-`@Decreases` sortedness) is proved by
  induction on `j - i` and then *used* at a call site to discharge a caller's
  postcondition — quantifier instantiation and all.

  **Not yet:** mutual recursion in the verifier (only direct self-recursion gives
  an inductive-hypothesis point — a cycle needs SCC-aware reasoning over a combined
  measure); and cross-module measure *inheritance* (an override of a precompiled
  super's `@Decreases`), which is the upstream groovy-contracts limitation, not a
  verifier one. Given induction and lemmas have landed, the item has outgrown
  "optional".
- **Heap/aliasing.** Don't. Groovy makes this very hard and the payoff is small
  for the fragment most developers care about.

---

## Phase 8 — Beyond SMT: proof by computation and proof hints

**A different axis from Phases 1–6.** Everything above widens the *fragment*
that gets encoded to Z3; the proof *mechanism* stays "collect obligations, hand
them to the solver". But SMT has a ceiling — most visibly Phase 6's trigger
cliff and the NIA opt-out — and the same ceiling exists in mature verifiers.
F\*, for instance, runs SMT by default but offers two escape hatches above it:
*symbolic computation* (prove by running an interpreter, not by equational
reasoning in the solver) and *tactics/metaprogramming* (full user-driven proof).
This phase records which of those are worth borrowing, and which are not — the
ordering is, as ever, by value against cost and fit with the project's
push-button, no-language-change identity.

### 8a — Normalisation: normalise-then-SMT *(the strongest candidate)*

**The escape hatch that fits Groovy's grain.** Many obligations are *closed
computations* that need no solver at all — you just run them. Groovy, unlike a
paper proof language, already ships an interpreter, so this is unusually cheap
to reach. A normalisation pre-pass slots in exactly where `Encoder.translate`
currently returns `null`:

- **Constant folding (closed sub-terms) — shipped.** A closed numeric
  sub-expression — `(2 + 2) * (2 + 2)`, a folded array index `a[(1 + 1) * 2]` — is
  reduced to a literal before encoding (`Encoder.tryFoldConstant`), dissolving the
  **NIA opt-out** for *constant* products that would otherwise be skipped. It
  reuses Groovy's own `ExpressionUtils.transformInlineConstants` (`NumberMath`
  semantics), so the fold matches Groovy's arithmetic and adds no new integer
  model — it stays consistent with the encoder's mathematical-`Int` view (the
  runtime-overflow gap is the separate bounded-int item). It is purely an
  accelerator: folding never produces a counterexample, so a wrong constant still
  refutes on the SMT side (tested).
- **Closed pure-function evaluation — shipped.** A small tree-walking interpreter
  (`PureEvaluator`) computes a *same-class, side-effect-free* function applied to
  *constant* arguments to a literal — `pow2(10)` → 1024, `factorial(5)` → 120 —
  whether the call appears in a contract or a body. It evaluates the *clean*
  CONVERSION body over the evaluable fragment (literals, parameters, `+ - * %`,
  comparisons, boolean connectives, `?:`/`if`/`return`, single-assignment locals,
  same-class recursive/static calls); anything else makes the call un-evaluable, so
  the verifier falls back to "skipped" — it never guesses. Purity is the
  conservative "body lies entirely in the fragment" proxy (no representable side
  effects); a step budget bounds non-terminating recursion; it computes with
  `long`, matching the encoder's mathematical-integer model (so it adds no new
  soundness gap beyond the existing bounded-int one). It's an accelerator — a
  wrong expected value still refutes on the SMT side (tested).
- **Bounded symbolic unfolding — next.** Partially unfold a pure function against
  *symbolic* arguments up to a `fuel` bound (F\*'s `fuel`/`ifuel`), handing the
  residual to Z3, so `pow2(n)` reduces against a symbolic `n`. Termination reuses
  the method-level `@Decreases` (Phase 7). This is the larger remaining half; the
  closed evaluation above is the shipped, sound first cut.

The clean architecture is **normalise-then-SMT**: evaluate what you can, send the
residual to the solver. One asymmetry to state plainly — normalisation helps only
the *positive* case. It produces no counterexample when a fact is false; it
computes a value or gets stuck. So it is a discharge *accelerator*, not a
replacement for the SMT path, and the project's headline counterexamples stay on
the SMT side.

**Costs that keep this far down, not soon:**

- **It enlarges the trusted base.** F\*'s normaliser is part of its TCB; a Groovy
  evaluator used for proof becomes trusted too, and must agree with the
  *compiled runtime* semantics. Fold `2 * pow2(11)` at arbitrary precision while
  the program runs on 32-bit `int` and the "proof" diverges from reality. This
  couples directly to the **bounded-integer / overflow** item above: evaluation
  and encoding must commit to the *same* integer model or the tool lies.
- **Purity and termination.** Only side-effect-free, terminating methods are safe
  to evaluate — exactly the property `@Decreases` already reasons about, so there
  is real synergy with [Phase 3](#phase-3--loops-invariant--decreases-shipped).

### 8b — Structured proof decomposition *(opt-in, philosophy-compatible)*

When one SMT shot can't reach a fact, let the author break the proof into steps
the solver *can* each discharge — Dafny-style `assert P by { ... }` and `calc`
chains — rather than writing a proof term. No new evaluator, no tactic language;
each intermediate assertion is just another VC. This composes with 8a (an
intermediate `assert` can be discharged by evaluation) and with Phase 6's
instantiation hints. It is the bounded, defensible cousin of tactics: control
when automation fails, without becoming a proof assistant.

### Not in scope here

Full interactive tactics and proof terms (the Coq/Lean/F\* `intro; split; qed`
style) are a **non-goal** — see below. They cut against "no language change,
push-button, diagnostics-not-dialogues", the same reasoning that rules out heap
and concurrency. The line this phase walks: borrow *hints* (8a, 8b, Phase 6
triggers) that keep the tool a compile-time checker; refuse the proof-term
language that would make it a different product.

---

## Phase 9 — Programmer-facing surface (authoring & diagnostics)

**Adoption, not capability.** Everything above is about *what* can be proved;
this is about whether a working Groovy developer understands what to write and
what it tells them back, without first learning formal-methods vocabulary. The engine speaks in *obligations*,
*counterexamples*, and an internal *size oracle* (`a.size`); a programmer who just
turned the checker on speaks in `.size()`/`.length`,
`ArrayIndexOutOfBoundsException`, and "what input breaks it?". The goal is to meet
them there — the same instinct that makes the rest of Groovy's static type checker
say "Cannot invoke method size() on null object" rather than naming an internal
AST node. A tool people understand is one they leave switched on.

The distinction that scopes this phase — **two kinds of diagnostic:**

- **Those with a well-known code/runtime equivalent.** Mirror it. An
  out-of-bounds obligation should read in the vocabulary of
  `ArrayIndexOutOfBoundsException` ("Negative array index [-1] too large for array
  size 0"), echo the accessor the programmer actually knows — `.size()` for
  collections/strings, `.length` for arrays (Groovy's universal size idiom) —
  rather than the internal `a.size` symbol, and ideally surface the counterexample
  as a **concrete failing call**: not `a.size = 0, i = -1` but `g(new int[0], -1)`
  — a runnable repro, the way a developer would demonstrate the bug themselves.
  The same applies to division (`ArithmeticException: Division by zero`) and null
  dereference (`Cannot invoke method size() on null object`).
- **Those with no code equivalent.** Loop-invariant establishment/preservation,
  termination, "could not decide", and the quantifier obligations of
  [Phase 6](#phase-6--quantifiers-shipped) have no runtime analogue to borrow. Forcing a
  fake one would mislead. Here the right move is *self-explanatory* verification
  vocabulary — name the obligation, say plainly what could not be shown and what
  would make it provable — not a runtime costume it does not fit.

**Authoring vocabulary — the input side of the same coin.** "Meet the programmer
where they are" applies to how specs are *written*, not only how failures are
*read*. Phase 6 introduces the quantifier as `Forall.range(0, a.length) { a[it] >= 0 }` — a static helper the encoder recognises, deliberately a plain Groovy
expression so it needs no language change and the runtime contract can still
evaluate it. But that is a bespoke verification idiom, and a Groovy developer
writing the *same thing* outside a contract would not invent it — they would
reach for the GDK they already know:

```groovy
(0..<a.length).every { a[it] >= 0 }      // a bounded IntRange + every
a.indices.every { a[it] >= 0 }           // the array's own index range
a.every { it >= 0 }                      // element-wise: `it` is the element
```

The leading Phase 9 candidate is therefore to **recognise these native idioms**
rather than `Forall.range`: `(lo..<hi).every {…}` and `xs.indices.every {…}` map
to the same bounded universal over indices, `xs.every { it … }` to a universal
over *elements* (`it` is `(select xs i)`), and `any` to the existential once that
lands. They are already executable (so the runtime contract works for free) and
read like ordinary Groovy — and they retire the `Forall` helper entirely. Cost
and caution: `every`/`any` are pervasive, so the encoder must treat them as
quantifiers **only in contract position** and only for the recognised
range/indices/collection shapes, and must keep the element-vs-index distinction
straight.

If that contract-position restriction proves fragile, the fallback is an
**annotation** surface rather than a method idiom — and there is precedent:
jqwik already uses `@Forall` for universal quantification in property-based
testing, so the spelling is familiar to Groovy/Java developers. An annotation is
unambiguous by construction (it is unmistakably a spec, never confused with an
in-the-wild `every`/`any` call), at the cost of reading less like an inline
boolean and composing less naturally with `&&` inside a larger contract. Like the
diagnostic wording, the right surface is best chosen *after* the quantifier shape
settles in Phase 6; `Forall.range` is the spike, not the committed syntax.

**Deliberately not done early.** Until the capability set settles (Phase 6
especially), new diagnostic and authoring shapes keep appearing, and pinning the
wording now would only churn. The internal `a.size` vocabulary stays for the moment — it is
accurate and internally consistent (the obligation and counterexample share the
symbol). When the time comes this is a `Reporter`-layer change — no engine or
solver risk — whose entire payoff is adoption: the gap between a tool people trust
and one they turn off because its errors read like a proof transcript.

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
- **Interactive tactics / proof terms.** The Coq/Lean/F\* style where the user
  drives the proof with `intro`/`split`/`qed` and builds an explicit proof term.
  This is the opposite of a push-button compile-time checker, and adopting it
  would make this a proof assistant rather than a better Groovy type-checker. The
  *bounded* borrows — instantiation hints and structured `assert … by`
  decomposition — live in [Phase 8](#phase-8--beyond-smt-proof-by-computation-and-proof-hints);
  the full tactic engine does not.
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
  which is great for `isqrt(-1)`. Once arrays are in scope (Phase 6), showing
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

The temptation is to do Phase 6 (quantifiers) early because the binary-search
example is so striking. The drop-off from "works on the example" to "works on
the next thing someone tries" is steepest there, so the foundation came first:
Phases 1 → 2 → 3 → 4, each catching a class of bug developers viscerally
recognise, none leaning on quantifier heuristics. Phase 5 (value-flow &
loop-fused safety) then followed — low-risk hardening that fixed the most
recognisable everyday gap inside the shipped fragment — *before* Phase 6
(quantifiers), which begins as its own multi-week effort, not a quick win bolted
onto a demo.
