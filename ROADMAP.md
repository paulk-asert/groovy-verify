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
Possible IndexOutOfBoundsException: index may be out of bounds
    obligation: 0 <= i && i < a.size()
    counterexample: a.size() = 0, i = -1
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
- **`xs.contains(y)`** — originally an *uninterpreted predicate* `contains$xs : Int -> Bool`
  (sound, `contains(y)` assumed entails `contains(y)` proved, but no membership reasoning).
  **Upgraded in Phase 9** to precise membership `∃ i. 0 <= i < xs.size ∧ xs[i] == y` over the
  modelled contents, once the existential `any` landed — so `contains` now relates to actual
  element values.

The seam grew `SmtBackend.boolVar` (nullity) here; `contains` first rode an
`uninterpretedPred`, since removed when Phase 9 re-modelled it as a precise
existential over the array contents.

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
  *assignment-implied* facts. Collection is also **short-circuit-aware**: in `p && q` the
  right operand's obligations are discharged under `p`, in `p || q` under `not p`, and a
  `c ? t : e` branch under `c`/`not c` — so `if (i > 0 && a[i] < a[i - 1])` proves `a[i - 1]`
  in bounds *from the `i > 0` to its left*, no nested-`if` workaround. And an array-element
  store (`a[i] = v`) no longer bails to the havoc fallback: its contents don't bear on the
  bounds/div/null obligations, so the pass collects the index and rhs obligations and carries
  on (this is what lets a recursive `insert` that swaps stay on the value-flow path).
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
static call / `getAt`. **Sort, revisited:** the *sortedness* half is now done — a
recursive insertion sort (`insert` + `sort`) verifies end-to-end via induction (see
Phase 7). What a *full* sort still needs is **permutation** (a multiset/`count` model
plus `old(a)` to relate the result to the input — without it, "sort" that zeroes the
array would pass) and, for a *loop*-based sort, nested-loop support; the recursive
formulation sidesteps the latter.

**Known limits.** Counterexamples for array/quantifier refutations show the
integer skeleton (`a.size`, indices) but not array contents or unconstrained
element values — honest, not yet concrete; the array-model pretty-printer
(cross-cutting risks) and the witness-as-failing-call idea (Phase 9) are the
follow-ups. UNKNOWN on a stalled quantifier stays a loud "could not decide"; the
user-supplied trigger/instantiation hint that would rescue it is the lightest
borrow from [Phase 8](#phase-8--beyond-smt-proof-by-computation-and-proof-hints).

---

## Phase 7 — Inter-procedural reasoning, induction & lemmas  *(shipped)*

Filed as an "optional heavy lift", this turned out to be the backbone of the Dafny-style
proofs — and it has landed. All of it reasons *modularly*: a callee's **contract** is used,
never its body.

- **Use a callee's `@Ensures` as a fact.** `int z = f(args)` assumes `f`'s postcondition
  with `result` bound to `z` and formals to actuals (same-class resolution by name + arity).
  A precondition check also assumes the `@Ensures` of the standalone call *immediately* before
  it, so `sort(a, n-1); insert(a, n-1)` composes — immediate-predecessor only, which is sound
  since nothing runs in between (a store between them would invalidate it, and does refute).
- **Induction over recursion.** A method may assume its *own* `@Ensures` at a recursive call —
  the inductive hypothesis — gated on a method-level `@Decreases` measure proved well-founded
  (`0 <= measure[args] < measure[entry]` at each call). It rides the stock `@Decreases`
  (GROOVY-12060), so it stays runtime-meaningful. No measure means the recursive result is
  opaque (honest "skipped"), never silently trusted.
- **Lemmas.** A `void` method proved by induction and *called for its `@Ensures`* — the
  proof-structuring primitive Dafny users lean on most. E.g. sortedness transitivity
  (`a[i] <= a[j]` for `i <= j` from adjacent sortedness, by induction on `j - i`) proved once
  and applied at a call site, quantifier instantiation and all.
- **Payoff — a verified sort.** A recursive insertion sort verifies its *sortedness*
  postcondition end-to-end: `insert` places `a[i]` into the sorted prefix (a store, by
  induction on `i`), `sort` composes on it (by induction on `n`). The recursive shape
  sidesteps nested loops entirely.

**Still not done here:** *permutation* for a real sort — needs a multiset/`count` model and
`old(a)` (the sortedness proof above is only the "zeroing the array would pass" half); mutual
recursion (only direct self-recursion gives an inductive-hypothesis point — a cycle needs
SCC-aware reasoning over a combined measure); and cross-module measure *inheritance* (an
override of a precompiled super's `@Decreases`), an upstream groovy-contracts limitation.

**Genuinely still optional, not done:**
- **Full NIA** — lift the "a product needs a literal operand" restriction (Z3's `qfnia` is
  incomplete; needs timeout discipline, maybe per-VC tactic selection).
- **Bounded-integer modelling** — catch overflow instead of silently working modulo 2^32
  (fixed-width bitvectors; every arithmetic VC gains a range side-condition, ~2x solver time).
  Bitwise / shift operators come for free with it.
- **Heap / aliasing** — don't. Groovy makes it very hard and the payoff is small for the
  fragment most developers care about.

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
- **Bounded symbolic unfolding — shipped.** A pure same-class function applied to
  *symbolic* arguments is inlined to its (single-expression) body with the arguments
  substituted, and the residual handed to Z3 — so `absV(x)` becomes an `ite` and a
  recursive `pow2(n)` reduces one level per call. A ternary body maps to Z3's `ite`
  (`Encoder` + backend gained `ite`/`uninterpretedFunc`). Recursion is bounded by a
  per-VC **fuel** budget (F\*'s `fuel`/`ifuel`); when it runs out — or the body isn't
  a single expression (an `if`/`return` chain like the statement form of `factorial`)
  — the unexpanded call is modelled as an *uninterpreted* integer function, a sound
  over-approximation (the result is constrained only through the levels actually
  unfolded). Inlining is faithful — a body that disagrees with the definition still
  refutes (tested). Two limits, both by design: it fires only for *contract-free*
  methods (a contracted callee is the inter-procedural/induction path's job, Phase 7),
  and because fuel only decrements, two applications of the same function in one
  obligation may unfold to different depths — proofs that rely on syntactically
  equating them belong to induction (Phase 7), not here.

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

The distinction that scoped this phase — **two kinds of diagnostic:**

- **Those with a well-known code/runtime equivalent — mirror it.** *(shipped)* Every refuted
  implicit-safety obligation now reads in the developer's vocabulary, not the engine's:
  - the head names the exception they'd actually hit — `Possible IndexOutOfBoundsException`,
    `Possible ArithmeticException: Division by zero`, `Possible NullPointerException: Cannot
    invoke method size() on null object` (the invoked method threaded from the call site;
    `IndexOutOfBoundsException` covers both arrays and lists without inferring which);
  - the obligation and counterexample echo the **accessor the developer wrote** — `a.length`,
    `xs.size()` — harvested by scanning their contracts/body (first spelling wins; a bare
    `a[i]` defaults to `.size()`, valid for arrays too), not the internal `a.size` symbol;
  - a **`fails on:`** line reconstructs a runnable input — `g(new int[0], -1)`, `d(0, 0)`,
    `n(null)`, and even pinned array contents (`diff([21239, 21238] as int[], 0)`) for a
    contents-dependent failure, while contents that don't matter stay size-filled (`new int[3]`).

  All but the array-element pinning are pure `Reporter`/presentation — the engine keeps `a.size`
  internally and the rename is applied once at the solver boundary. The repro additionally reads
  boolean (nullity) and `select(arr, k)` values from the model (a small, contained `Z3Backend`
  touch) and is labelled best-effort: a field-dependent failure may not reproduce from it, and
  String contents / arbitrary objects stay unsynthesised. The **UNKNOWN** ("could not decide")
  head keeps its verification vocabulary — that case has no runtime analogue to borrow.
- **Those with no code equivalent.** Loop-invariant establishment/preservation, termination, and
  the quantifier obligations have no runtime analogue. Forcing a fake one would mislead; the
  right move is *self-explanatory* verification vocabulary — name the obligation and say plainly
  what could not be shown.

**Authoring vocabulary — the input side.** *(shipped)* "Meet the programmer where they are"
applies to how specs are *written* too. The bespoke `Forall.range(...)` helper is now joined by
the native GDK idioms a Groovy developer already reaches for, recognised in contract position and
lowered onto the same bounded `forall`:

```groovy
(0..<a.length).every { a[it] >= 0 }   // bounded range over indices
a.indices.every { a[it] >= 0 }        // the array's own index range
a.every { it >= 0 }                   // element-wise: `it` is the element
```

These need no import and stay runtime-evaluable, so they also work inside `@Invariant` (retiring
the `verification.Forall` FQN + typed-index warts the loop case forced). Recognition is
shape-restricted — any other `every` falls through to a loud "outside fragment" skip, never
silently reinterpreted.

The **existential `any` is now shipped** too — `a.any { it < 0 }`, `(lo..<hi).any { … }`,
`xs.indices.any { … }` — lowered to a bounded `∃ i. lo <= i < hi ∧ body` (a shared
`emitQuantifier` with `every`; `Z3Backend.exists` mirrors `forall`). It also **upgrades
`xs.contains(y)` from the opaque Phase-4 uninterpreted predicate to precise membership** —
`∃ i. xs[i] == y` over the modelled contents — so `contains` now relates to actual element
values (e.g. `xs.contains(xs[k])` is provable for a valid `k`). Two notes from building it: (1)
a bounded existential *goal* needs a ground witness term for Z3 to instantiate (e-matching won't
invent one), which the natural specs supply; (2) a quantifier trigger must mention a bound
variable — a body that indexes by a *different*, ground index (`any { it == a[k] }` → ground
`a[k]`) was polluting the pattern, now filtered in `Z3Backend`. Authoring relies on
GROOVY-12059 (nested closures in contract conditions, including `@Ensures`), in the ASF
snapshot. Still open: full retirement of the `Forall` helper (migrating its remaining internal
uses); `Forall.range` still works for back-compat. If the contract-position restriction ever
proves fragile, the documented fallback is an annotation surface (`@Forall`, with jqwik
precedent) — unambiguous by construction, at the cost of reading less like an inline boolean.

**Why it waited.** Pinning diagnostic/authoring wording before the capability set settled
(Phase 6 especially) would only have churned. With the surface now landed, the payoff is
adoption: the gap between a tool people trust and one they turn off because its errors read like
a proof transcript.

---

## Phase 10 — Instance methods & field state  *(shipped)*

The fragment was static-function-shaped; this opens it to ordinary OO code, in two layers.

**Layer A — instance methods, parameter contracts (already worked).** Nothing in the verifier
gated on `static`, so a non-`static` method with `@Requires`/`@Ensures` over its parameters
verifies exactly like a static one. Confirmed with a test; no code change.

**Layer B — instance field state (shipped).** A method may now read and write its receiver's
*scalar* fields:
- **Reads** — `this.count` (a `PropertyExpression` on `this`) and the bare `count` both resolve to
  the field's state variable, in contracts and bodies.
- **Writes** — `this.count = …` / `count = …` thread the field forward, via **SSA**: each
  assignment binds the name to a fresh version, so a method's `@Requires` sees the *entry* value
  and its `@Ensures` the *exit* value. `count = count + 1` becomes `count#1 == count + 1`, not the
  false `count == count + 1`. This dropped the old single-assignment-locals restriction, so
  re-assigned locals now work too; SSA versions are hidden from the displayed counterexample.

So a mutator is proven to maintain its bound — `@Requires({ count < max }) @Ensures({ count <= max })
void inc() { count = count + 1 }` verifies, and the same without the guard refutes (`count = max`,
the entry/exit distinction made visible). Framing within a single method is trivial (unwritten
fields are unchanged); the receiver's fields are assumed unaliased, the same boundary arrays draw.

**Not yet:** class-level `@Invariant` (object invariants — assume on entry, prove on exit; its own
capture infrastructure) and *cross-method* field effects, which is the `@Modifies`/framing slice.
(Array-typed fields work already — `a[j] = v` on a field threads through `arrayFor` like a param.)

---

## Phase 11 — Pre-state: `old`  *(shipped)*

A postcondition can now relate the *exit* state to the *entry* state via groovy-contracts' `old`
map. `old.field` reads the field's value at method entry; `old.a[i]` reaches into the entry
*contents* of an array field. The verifier captures the snapshot in `checkPath` *before* the body's
writes SSA-rebind state forward, binding `old$field` to the entry value (scalar and array views
both pinned). `@Ensures({ count == old.count + 1 })` verifies for `count = count + 1`, and the
mismatched `count = count + 2` refutes.

This is the keystone the framing/permutation arc needed. The headline is the **element frame**:
a setter that writes only `a[j]` proves every other element is left alone —
`@Ensures({ (0..<a.length).every { it == j || a[it] == old.a[it] } })` — which is exactly the
shape `@Modifies` will lean on so that sound array-havoc-on-call doesn't lose the elements a callee
didn't touch (the gap that would otherwise break the recursive insertion sort).

`old` is instance-only upstream (GROOVY-12052: it snapshots instance state, unsupported in static
methods), so it builds on the Phase 10 field support. It is fully dual-purpose: groovy-contracts
*clones* `Cloneable` fields for the runtime `old` map, and arrays are `Cloneable`, so for `int[]`
the runtime snapshot matches the verifier's entry-snapshot model. **Not yet:** `old` over a
multiset/`count` (the permutation step), and `old` of method *parameters* (upstream models only
fields).

---

## Phase 12 — Permutation: multiset / `count`  *(building block shipped)*

The half a sort is missing beyond *sortedness* is *permutation* — that the output is a rearrangement
of the input. The tractable encoding, which sidesteps the unbounded `∀v` a multiset usually needs:

- **`count`** — Groovy's GDK `a.count(v)` (occurrences of `v`) modelled as an uninterpreted
  `count(arr, v) : (Array, Int) -> Int` (`SmtBackend.count`). `old.a.count(v)` is the entry snapshot.
- **Per-store update law** — on every `a[i] = val`, `checkPath` asserts
  `count(store(a,i,val), v) = count(a, v) - [a[i]==v] + [val==v]` for the values `v` the postcondition
  counts. This is the sound semantics of `count` under one store; nothing else axiomatises it.
- **Ghost value parameter** — a method takes a value param `v` and proves
  `@Ensures({ a.count(v) == old.a.count(v) })`. Since `v` is an arbitrary free parameter, proving it
  for `v` *is* proving it for all values — permutation, with **no quantifier in the SMT**.

A **swap** is two stores whose count updates cancel, so it preserves every count — verified — while a
plain copy (drops an element) refutes. That building block is sound and shipped.

**Co-dependency found with `@Modifies`.** The *recursive* sort's permutation does **not** yet hold
soundly: when a caller assumes a callee's `@Ensures` that mentions `old.a`, the assume path resolves
`old.a` to the *caller's* entry snapshot, not the array *at the call* — so the recursion's count
clause becomes an inconsistent (vacuous) assumption (a broken overwrite-`insert` wrongly "verified",
which is how this was caught). Binding a callee's `old` to a *call-site* snapshot is precisely the
`@Modifies`/havoc machinery. So permutation's recursive composition and `@Modifies` are mutually
dependent and land together: `@Modifies` brings sound inter-procedural `old`, which makes the full
insertion sort verify *sorted ∧ permutation* — and the permutation clause is in turn what lets
`insert` survive the sound array-havoc (it supplies the bound on the sorted prefix that sortedness
alone can't). The per-store `count` law built here is the standalone, sound foundation for that.

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
