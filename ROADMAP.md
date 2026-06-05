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
(existentials followed in Phase 9; unbounded quantifiers stay out of scope).

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
static call / `getAt`. **Sort, revisited:** the *sortedness* half lands here — a
recursive insertion sort (`insert` + `sort`) verifies end-to-end via induction (see
Phase 7). The other half, **permutation** (a multiset/`count` model plus `old(a)`), and the
sound framing that lets the two compose in place, followed in Phases 12–14 — where the full
sort verifies *sorted ∧ permutation*. (A *loop*-based sort would also need nested-loop
support; the recursive formulation sidesteps it.)

**Known limits.** Counterexamples for array/quantifier refutations show the
integer skeleton (`a.size`, indices); Phase 9 since added pinning of
solver-constrained array *contents* and a runnable `fails on:` repro, though
unconstrained element values and a full array-model pretty-printer (cross-cutting
risks) stay open. UNKNOWN on a stalled quantifier stays a loud "could not decide"; the
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

**Not done *here* (since shipped in Phases 12–14):** *permutation* for a real sort — the
multiset/`count` model and `old(a)` the sortedness proof above leaves out (it is only the
"zeroing the array would pass" half). Still genuinely open: mutual recursion (only direct
self-recursion gives an inductive-hypothesis point — a cycle needs SCC-aware reasoning over a
combined measure); and cross-module measure *inheritance* (an override of a precompiled super's
`@Decreases`), an upstream groovy-contracts limitation.

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

- **Constant folding (closed sub-terms) — shipped.** A closed numeric sub-expression —
  `(2 + 2) * (2 + 2)`, a folded array index `a[(1 + 1) * 2]` — is reduced to a literal via
  `Encoder.tryFoldConstant` before encoding, dissolving the **NIA opt-out** for *constant* products.
  Reuses Groovy's own `ExpressionUtils.transformInlineConstants` (`NumberMath` semantics) so the
  fold matches Groovy's arithmetic.
- **Closed pure-function evaluation — shipped.** A tree-walking interpreter (`PureEvaluator`)
  computes a *same-class, side-effect-free* function applied to *constant* arguments to a literal —
  `pow2(10)` → 1024, `factorial(5)` → 120 — whether the call appears in a contract or a body. It
  evaluates the *clean* CONVERSION body over the evaluable fragment (literals, parameters,
  `+ - * %`, comparisons, boolean connectives, `?:`/`if`/`return`, single-assignment locals,
  same-class recursive/static calls); anything else makes the call un-evaluable and the verifier
  falls back to "skipped" — never guesses. Purity proxy: "body lies entirely in the fragment";
  step budget bounds non-terminating recursion.
- **Bounded symbolic unfolding — shipped.** A pure same-class function applied to *symbolic*
  arguments is inlined to its (single-expression) body with arguments substituted — so `absV(x)`
  becomes an `ite` and a recursive `pow2(n)` reduces one level per call. Recursion bounded by a
  per-VC **fuel** budget (F\*'s `fuel`/`ifuel`); when it runs out — or the body isn't a single
  expression — the unexpanded call is modelled as an *uninterpreted* integer function, a sound
  over-approximation. Fires only for *contract-free* methods (a contracted callee is Phase 7's
  inter-procedural path). **Phase 25 upgrade:** a recursive call now becomes a *shared* symbol
  `f#(args)` carrying its **defining equation**, so two applications are the same term by
  congruence and inductive proofs over a recursive contract function go through.

All three are pure accelerators — a wrong value still refutes on the SMT side (tested for each).
Evaluation computes with `long`, matching the encoder's mathematical-`Int` view, so they add no
new soundness gap beyond the existing bounded-int one.

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
`xs.indices.any { … }` — lowered to a bounded `∃ i. lo <= i < hi ∧ body`. It also **upgrades
`xs.contains(y)` from the opaque Phase-4 uninterpreted predicate to precise membership**
(`∃ i. xs[i] == y` over the modelled contents) — so `contains` now relates to actual element
values (e.g. `xs.contains(xs[k])` is provable for a valid `k`). Authoring relies on
GROOVY-12059 (nested closures in contract conditions) in the ASF snapshot. `Forall.range` still
works for back-compat; migrating its remaining internal uses is the open follow-up.

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

**Class-level `@Invariant`** (the natural next layer for OO code) was originally listed as the open
piece here; the **instance-method slice landed in Phase 15a** (see below). *Cross-method* field
effects — the `@Modifies`/framing slice — followed in Phase 13. (Array-typed fields work already —
`a[j] = v` on a field threads through `arrayFor` like a param.)

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
shape `@Modifies` leans on (Phase 13) so that sound array-havoc-on-call doesn't lose the elements a
callee didn't touch (the gap that would otherwise break the recursive insertion sort).

`old` is instance-only upstream (GROOVY-12052: it snapshots instance state, unsupported in static
methods), so it builds on the Phase 10 field support. It is fully dual-purpose: groovy-contracts
*clones* `Cloneable` fields for the runtime `old` map, and arrays are `Cloneable`, so for `int[]`
the runtime snapshot matches the verifier's entry-snapshot model. **Not yet:** `old` of
method *parameters* (upstream models only fields). (`old` over a multiset/`count` — the permutation
step — followed in Phase 12.)

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

**Co-dependency found with `@Modifies` (since resolved).** At this point the *recursive* sort's
permutation did not hold soundly: when a caller assumes a callee's `@Ensures` that mentions `old.a`,
the assume path resolved `old.a` to the *caller's* entry snapshot, not the array *at the call* — so
the recursion's count clause became an inconsistent (vacuous) assumption (a broken overwrite-`insert`
wrongly "verified", which is how this was caught). Binding a callee's `old` to a *call-site* snapshot
is precisely the `@Modifies`/havoc machinery, built in Phase 13 — which closed this, so the full
insertion sort verifies *sorted ∧ permutation* in Phase 14. The per-store `count` law built here is
the standalone, sound foundation for that.

---

## Phase 13 — Frame conditions: `@Modifies`  *(shipped)*

A method declares the caller-visible locations it may change via groovy-contracts'
`@Modifies({ this.field })` / `@Modifies({ [this.a, this.b] })` / `@Modifies({ param })`. Captured
like the other contracts (a `modifies` member on `@ContractSource`).

**Frame-check (shipped).** A method carrying `@Modifies` is verified to write *only* the locations
it lists — every `a[i] = v` (array `a`), `this.x = v` / bare field `x = v` is checked against the
declared set; local writes don't count. `@Modifies({ [] })` means pure (any field/array write is a
loud error). This is the callee-side half: a method honours its own frame.

**Caller-side framing (shipped).** At a call to a method with `@Modifies`, the caller now *havocs*
the declared locations (fresh symbols) and reframes them from the callee's `@Ensures` — binding the
callee's `old.X` to the value *at the call*, not the caller's own entry snapshot. That last point was
the bug Phase 12 surfaced (a callee's `old.a` resolving to the caller's entry made the recursion's
`count` clause vacuous; a broken overwrite-`insert` wrongly verified). With it fixed:
- the cross-call **"clobber"** unsoundness is closed — a caller can no longer assume an array a callee
  may modify is unchanged (verified: a caller relying on `a[0]` across a clobbering call now refutes);
- a `@Modifies`-only callee (no `@Ensures`) is modelled as a pure havoc of the declared locations
  (`resolveContractedCallee` widened to accept it);
- the recursive insertion sort is proven a **permutation** for real — `a.count(v) == old.a.count(v)`
  holds across the swaps *and* the recursive calls — and the broken overwrite now refutes.

---

## Phase 14 — The fully verified sort: *sorted ∧ permutation*  *(shipped; precondition hardened in Phase 24)*

> **Hardened by Phase 24** — the `insert` recursive precondition had been passing vacuously
> (name-conflation); restored with a one-line `maxBound` lemma. Now sound at every obligation.

The capstone. A recursive in-place insertion sort proven **both** correctness halves at once —
the result is sorted *and* a permutation of the input — under sound `@Modifies` framing (every call
havocs the array and reframes it from the callee's `@Ensures`; nothing is assumed unchanged for
free). No new engine machinery: it composes bounded quantifiers (Phase 6/9), induction via
`@Decreases` (Phase 7), the per-store `count` law (Phase 12), `old` pre-state (Phase 11), and
caller-side framing (Phase 13) into a single result. See the README's "fully verified sort".

The sortedness-under-havoc problem flagged at the end of Phase 13 — after the recursive call havocs
`a`, proving `a[m-1] <= a[m]` — is solved without a range-multiset: the recursion passes the **pivot
`a[m]` itself** as a fresh, *tight* upper bound `hi`, so the sorted prefix the recursion returns is
bounded by exactly the element it must sit below. A ghost value `v` carries the multiset
(`a.count(v) == old.a.count(v)` for arbitrary `v`), and a suffix-frame clause (`(m+1..<a.length).every
{ a[it] == old.a[it] }`) preserves the untouched tail across the havoc. Soundness is anchored: a
no-op sort cannot claim its result is sorted, and an overwriting insert (Phase 12) cannot claim the
permutation.

---

## Phase 15a — Class `@Invariant`: instance methods  *(shipped)*

The natural OO follow-on to Phase 10's instance fields: a `@groovy.contracts.Invariant({ ... })` on a
class is an **object invariant** — at runtime it holds after every constructor and before/after every
method call. The verifier now treats the class-level form as an extra exit obligation for each
non-static instance method: **assumed at method entry** (an extra fact in scope, alongside `@Requires`)
and **proved at method exit** (conjoined into the goal that `@Ensures` carries, or — for void methods
with no `@Ensures` — standing as the sole exit obligation).

**How it works:**

- **Capture.** A sibling of `ContractExpansionTransform.augment` walks `cn.annotations` at CONVERSION,
  reads each `@Invariant` closure's verbatim text via the same `SourceText` path as
  `@Requires`/`@Ensures`, and attaches a runtime `@ClassInvariantSource` carrier (separate from the
  method-level `@ContractSource` to keep its target narrow). Both the repeatable `@Invariant`
  sequence and the `@Invariants` container shape are handled.
- **Resolve.** `VerifyChecker.classInvariantTexts(ClassNode)` walks the superclass chain super-first
  and returns each captured text re-parsed to an `Expression`. Parent invariants are AND-conjoined
  with the subclass's — matching groovy-contracts' upstream semantics.
- **Pre-filter.** `beforeVisitMethod` pre-translates each invariant in a probe session and drops any
  that don't encode (e.g. `name.length() > 0` on a String field — outside the fragment). One
  `Skipped class invariant` diagnostic per dropped clause per method, not one per discharge site.
- **Wire.** `assumeClassInvariants(s, enc)` is the single helper called from every discharge site:
  - `checkPath` — entry-assume + exit-conjoin (postcondition path).
  - `assumeContext` / `dischargeVfObligation` / `dischargeSeeded` — entry-assume for the
    implicit-obligation discharge (Phase 1/5 paths).
  - `checkEstablishment` / `checkPreservation` / `checkProgress` / `checkUse` — entry-assume for the
    four loop VCs.
- **Diagnostic.** `Reporter.formatClassInvariantViolation` emits the dedicated
  `Cannot prove class invariant of <method> holds at method exit` head when the invariant is the
  sole reason for refutation; `formatClassInvariantSkipped` for outside-fragment clauses.

```groovy
@groovy.contracts.Invariant({ count >= 0 })
class Counter {
    int count
    void inc() { count = count + 1 }                          // verifies: invariant preserved
    void dec() { count = count - 1 }                          // REFUTED: count = 0 → -1
    @Requires({ count > 0 }) void safeDec() { count = count - 1 }   // verifies under the guard
}
```

**Soundness scope.** Sound by construction at *method-entry points* (establishment, postcondition
goal, implicit-obligation seed). For the loop **preservation/progress** VCs the invariant is also
in scope, which is sound iff the loop body doesn't write to a field the invariant references — the
same caveat already in place for the body-internal obligation discharge. A future frame analysis
(per-loop, analogous to `@Modifies` for methods) tightens this; until then, users putting actively-
mutated fields in a class invariant should anticipate the limitation.

**Not yet (15b/15c):**
- **Constructors establishing the invariant.** Shipped in Phase 15b below.
- **Cross-class call-site assumption.** At a call `caller.someOther.m(...)`, the callee's class
  invariant can be assumed to hold both before and after — natural extension of `assumeCalleeEnsures`
  in Phase 13. 15c.
- **Cross-module class-invariant transport.** Same producer-recompile discipline as method
  `@Requires`: a producer compiled without groovy-verify won't carry the class-invariant text in
  bytecode. 15c.

---

## Phase 15b — Class `@Invariant`: constructors establish the invariant  *(shipped)*

**Closes the "instance methods only" qualifier Phase 15a left.** Phase 15a treated `@Invariant` as
an extra entry-assumption + exit-obligation for every non-static method. Constructors got nothing:
the capability table read "instance methods" with that asterisk visible to anyone evaluating the
framework. Now a constructor proves the invariant *at exit* (no entry-assume — the invariant is the
goal, not a precondition), so the class is verified valid by construction.

**Three things made it work:**

- **Constructor capture.** `ContractExpansionTransform` now iterates `cn.declaredConstructors`
  alongside `cn.methods`, attaching the same `ContractSource` annotation + clean-body snapshot.
- **`afterVisitClass` sweep.** Groovy's `StaticTypeCheckingVisitor` doesn't dispatch constructors
  through the `beforeVisitMethod`/`afterVisitMethod` hooks — silent skip. `VerifyChecker` now
  overrides `afterVisitClass(ClassNode)` and manually invokes the same setup + verify pipeline for
  each constructor, with a `currentIsConstructor` flag that makes `assumeClassInvariants` a no-op
  at entry (the invariant is the goal, not a fact).
- **Int-field default-init.** A `Counter()` with an empty body trivially satisfies
  `@Invariant({ count >= 0 })` at runtime (JVM zeroes Int fields before the constructor body),
  but without default-init the field would be unconstrained and refute. `initFieldDefaults`
  asserts `field == 0` at constructor entry for each Int-like instance field. Reference / Set /
  Map / array fields are left unconstrained — the constructor body is expected to initialise them
  when the invariant requires.

```groovy
@groovy.contracts.Invariant({ count >= 0 && count <= max })
class Counter {
    int count, max
    @Requires({ m > 0 })
    Counter(int m) { max = m }                              // verifies — count is default 0, max = m > 0
    @Requires({ count < max })
    void increment() { count = count + 1 }                  // verifies — Phase 15a path
}
```

Drop the `@Requires({ m > 0 })` and the constructor refutes (count >= 0 holds, but max >= count
needs max >= 0 — m could be negative). A `Counter(int n) { count = n }` without
`@Requires({ n >= 0 })` likewise refutes, with `fails on: <init>(-1)` from the model.

**Known limits:**

- **Field initializers.** Groovy compiles `int count = 5` into a synthetic init block prepended to
  every constructor. The clean-body snapshot may or may not contain that injected code; the first
  cut here trusts the constructor body to explicitly assign anything the invariant requires.
  Field initializers as a verified path is a future polish.
- **`<init>` in the diagnostic.** The refute message names the constructor by its JVM-internal
  `<init>` name; a small Reporter tweak could surface the source-level class name (`Counter(-1)`).
- **Cross-class call-site invariant assumption** (when a *consumer* method calls into a class with
  an invariant) remains deferred to 15c. Within a single class, the constructor's exit invariant
  becomes the entry assumption for every other method via Phase 15a's assume-at-entry mechanism;
  cross-class needs the same callee-side invariant lookup applied at the call site.

---

## Phase 16 — Finite sets: membership + cardinality law  *(shipped)*

**The first genuinely new *data structure*, and the foundation under reasoning about reachable-set
algorithms (DFS, worklists, dedup).** Everything before this modelled integers, sequences (arrays /
lists by index), and scalar field state. A `set<T>` is the data structure those proofs are actually
built on — a value that only grows, a membership test, and a cardinality that drives termination —
and it is also everyday Groovy. This lands it for the common, tractable case.

**The encoding — sets as characteristic arrays, the in-grain choice.** A `Set<Integer>` is an
`Array Int -> Int` characteristic function (`1` = member, `0` = absent), so the three core operations
reuse Z3's array theory wholesale rather than introducing a new theory:

- **membership** — `x in s` / `s.contains(x)` → `(select s x) == 1`;
- **add / remove** — `s.add(x)` / `s.remove(x)`, threaded through the body as `s := (store s x 1|0)`
  exactly like an array store, so a later membership read of the post-state resolves through the
  store/select axioms for free (no quantifier);
- **cardinality** — `s.size()` is an uninterpreted `(Array) -> Int` (`setCard`, the direct analogue of
  Phase 12's `count`), whose meaning comes **only** from a per-mutation update law asserted at each
  add/remove: `card(add(s,x)) = card(s) + (x in s ? 0 : 1)`, `card(remove(s,x)) = card(s) - (x in s ? 1 : 0)`.

This is the quantifier-free heart of the recommendation: the same "uninterpreted measure + per-operation
update law" pattern that made permutation provable without `∀v` in Phase 12, now applied to a set's size.
A method that adds an element known *fresh* (`@Requires({ !(x in s) })`) proves `s.size() == old.s.size() + 1`;
drop the freshness premise and the `+ 1` rightly refutes (`x` may already be present). That `size`-grows-by-one
law is precisely what a set-valued `@Decreases` measure (`N - visited.size()`) needs.

**How it works:**

- The encoder is otherwise *shape-based and untyped*, but set and list operations are syntactically
  identical (`contains`, `size`, `in`, `+`). So `VerifyChecker` computes the set-typed parameter/field
  names (`collectSetNames`, `Set`-implementing declared types) and hands them to the `Encoder`
  (`setNames`) — the one place a type hint is needed. A receiver in that set lowers to set semantics;
  anything else stays on the list/array path.
- Body mutation rides the existing path machinery: a standalone `s.add(x)` is captured as a `LemmaCall`
  and intercepted in `checkPath` (`applySetMutation`) ahead of the inter-procedural lemma path, threading
  the store and asserting the cardinality law — no new `BodyEncoder` step kind.
- `old.s` is snapshotted as a set (entry handle) alongside the scalar/array snapshots, so
  `x in old.s` / `old.s.size()` read the entry value. `@Modifies` is honoured on both sides: a set
  mutation is frame-checked as a write to `s` (an undeclared `s.add` under `@Modifies({})` is a loud
  error), and a modified set field is havoced + reframed at a call site like an array.

```groovy
class C {
    Set<Integer> s
    @Requires({ !(x in s) })
    @Modifies({ this.s })
    @Ensures({ x in s && s.size() == old.s.size() + 1 })
    void put(int x) { s.add(x) }                 // verified
}
```

**Known limits (the honest edges).**

- **Element domain is `Int`.** A `Set<Integer>` (node ids, keys) is modelled; `Set<String>` /
  `Set<Object>` would need an element→Int mapping (Route 2 in the design notes), not done.
- **Set *algebra* stays out of fragment.** Union / intersection / subset (`s.containsAll(t)`,
  `s + t`, `s <= t`) need an unbounded `∀x. x∈s ⇒ x∈t` — the explicit quantifier non-goal — so they
  emit a loud "skipped", never a silent pass. The bounded-domain `every`-over-`0..<N` lowering that
  would bring subset into the fragment is the natural next slice.
- **Maps** build directly on this phase (a key-*set* that is itself a set) — shipped in Phase 17 below.

**Wired into recursion termination.** The cardinality law now drives a recursive `@Decreases` measure: the
termination replay (`dischargeTermination`) threads each `s.add(x)` / `s.remove(x)` through the per-mutation
law and translates the *entry* measure before those effects, so a set-valued measure like `n - s.size()`
strictly decreases across a recursive call exactly when a fresh element was added. This is the
DFS-shaped termination argument — a finite recursion over a bounded domain that ends because the visited
set keeps growing — proved with **no quantifier**:

```groovy
class C {
    Set<Integer> s; int n
    @Modifies({ this.s })
    @Decreases({ n - s.size() })
    void fill(int x) {
        if (!(x in s) && s.size() < n) {   // x is fresh, room remains
            s.add(x)                       // |s| grows by one (the cardinality law)
            fill(x + 1)                    // measure n - |s| strictly decreases
        }
    }
}
```

Drop the `!(x in s)` freshness guard and `s.add(x)` may be a no-op, so the measure need not decrease —
termination rightly refutes (`fails on: fill(4)`). The termination half — historically the hard part,
since cyclic graphs make naive DFS loop forever — is done.

---

## Phase 17 — Finite maps: value array + key-set  *(shipped)*

**The DFS adjacency representation — and it cost almost no new machinery, because a map decomposes into
two things this project already has.** A `Map<Integer,Integer>` is modelled as a **value array** (its
contents, `m[k]`) *plus* a **key-set** (its domain) — and the key-set is exactly the Phase-16 set, so
`m.containsKey`, `m.size()`, and the cardinality law come straight from the set machinery.

**The encoding:**

- **value lookup** — `m[k]` / `m.get(k)` → `(select vals k)` over the value array;
- **key membership** — `k in m` / `m.containsKey(k)` → set membership on the key-set;
- **put** — `m.put(k,v)` / `m[k] = v` does *both* sides at once (`doMapPut`): `vals := (store vals k v)`
  **and** the key-set add `keys := (store keys k 1)` with the per-mutation cardinality law. So after a
  put: `m[k] == v` (value read), `m[j] == old.m[j]` for `j != k` (the value frame, via array theory), and
  `m.size()` grew by one **iff** `k` was a new key;
- **size** — `m.size()` → `card(keys)`, reusing the set cardinality and its law unchanged.

**How it works:** the same shape-based-encoder-needs-a-type-hint story as sets — `VerifyChecker` collects
the `Map`-typed names (`collectMapNames`) and hands them to the `Encoder`, which routes a subscript /
`in` / `.get` / `.containsKey` / `.size` on those names to map semantics. Both put spellings ride the
existing path machinery (`m.put` as a `LemmaCall`, `m[k] = v` as the `ArrayStore` step), and a map
subscript is **excluded** from the array-bounds obligation — `m[k]` is a key lookup, not an index. `old.m`
snapshots both dimensions; `@Modifies` frame-checks a `put` and havocs/reframes a modified map across a
call, like an array. And the **key-set cardinality drives a recursive `@Decreases` measure** the same way
sets do — `n - m.size()` strictly decreases when a fresh key is inserted (the map twin of the DFS
termination above).

```groovy
class C {
    Map<Integer,Integer> m
    @Requires({ j != k })
    @Modifies({ this.m })
    @Ensures({ m[k] == v && m.containsKey(k) && m[j] == old.m[j] })
    void put(int k, int v, int j) { m.put(k, v) }     // verified
}
```

**Known limits.** Int keys and Int values only (`Map<Integer,Integer>`). The two pieces a *full* DFS over
`map<Node, set<Node>>` still wants: **(a)** nested values — a map whose values are themselves sets
(`Map<K, Set<V>>`), i.e. a value array of *set* handles (nested arrays, modellable but not yet wired); and
**(b)** the reachability **functional** postcondition (every reachable node ends visited), a bounded-domain
`every` over the adjacency relation. Value-search ops (`containsValue`) and `keySet()`/`values()` as
first-class collections stay a loud skip. With sets, maps, and the cardinality measure all in place, those
two are the remaining gap between here and a fully verified DFS — and both are additive, no engine rework.

---

## Phase 18 — Reachability: the recursive graph traversal  *(shipped)*

**The property a search algorithm exists for — and it composed from the previous phases with no new engine
code.** A depth-first traversal of a functional graph (`next : Map<Node,Node>`, the successor) that marks
nodes in a `Set<Node>`, with a reachability postcondition proved by induction. The notable part is that
sets (Phase 16), maps (Phase 17), induction via `@Decreases` (Phase 7), caller-side set framing (Phase 16),
and bounded quantifiers (Phase 9) *already* compose to discharge it — this phase is the demonstration, not
new machinery.

**What is proved (the two halves the bounded fragment expresses soundly):**

- **Soundness — `visited` only grows.** `(0..<n).every { !(it in old.visited) || (it in visited) }`: a
  bounded universal over the node domain saying every previously-visited node stays visited. The recursive
  call havocs `visited` (sound `@Modifies`) and reframes it from the callee's `@Ensures`; the self-`@Ensures`
  is the inductive hypothesis, and the store relation `visited1 = visited0 ∪ {u}` chains through it.
- **Progress — the node handed in ends visited.** `fuel <= 0 || (u in visited)`: under a fuel budget (a
  plain-int `@Decreases`), the traversed node is covered. On the base case it is already present; on the
  step it is added before the recursion, and monotonicity carries it across the havoc.

Both halves hold under a fuel measure; the soundness half also holds under the **set-cardinality measure**
`@Decreases({ n - visited.size() })` — the DFS-shaped termination from Phase 16 — proving the two
contributions (a cardinality-terminating recursion *and* a reachability postcondition) compose. A traversal
that *removes* a node refutes the monotonic-growth clause; claiming coverage *unconditionally* (dropping the
`fuel <= 0` guard) refutes, because the budget can run out.

```groovy
@Requires({ 0 <= u && u < n && (0..<n).every { 0 <= next[it] && next[it] < n } })
@Modifies({ this.visited })
@Decreases({ fuel })
@Ensures({ (0..<n).every { !(it in old.visited) || (it in visited) } &&
           (fuel <= 0 || (u in visited)) })
void visit(int u, int fuel) {
    if (fuel > 0 && !(u in visited)) { visited.add(u); visit(next[u], fuel - 1) }
}
```

**The honest boundary — what is *not* proved, and why.** Two reachability properties stay out of reach, both
recorded as future work because each needs a genuinely new capability, not just more wiring:

- **Unconditional progress / `start ∈ visited` for an *unbounded* (cardinality-terminating) DFS.** The
  cardinality measure forces the guard `visited.size() < n` (so the recursion is well-founded), which means
  the method legitimately stops when `visited` is "full". To conclude the node is nonetheless covered, you
  need the **domain-cardinality fact**: for `S ⊆ {0..n-1}`, `|S| ≤ n`, and `|S| = n ⇒ S = {0..n-1}`. The
  uninterpreted `card` (Phase 16) knows only its per-mutation deltas, not this relation to the domain. The
  fix is a bounded **cardinality axiom** — e.g. `card(S)` defined as `Σ_{i<n} (i ∈ S ? 1 : 0)`, a bounded
  sum tying cardinality to membership over `0..<n` — the natural next increment for set reasoning.
- **Completeness — every reachable node is visited (the closure fixpoint).** This is the deep half of DFS
  correctness. It is *not* a simple inductive set property: the invariant DFS actually maintains is "`visited`
  is closed under successors **except** for nodes on the current recursion stack", so it needs the stack
  modelled (a sequence/ghost), or an explicit inductive `IsPath` predicate plus a least-fixed-point argument
  — beyond the bounded-quantifier fragment. This is the same frontier subtlety that makes DFS a showcase
  proof in Dafny, and is left as an explicit non-trivial target.

Net: the **termination** half of DFS (Phases 16/17) and the **soundness + bounded-progress** reachability
postconditions (this phase) are done and sound; **completeness** and **unconditional coverage** are the two
named, well-understood gaps remaining — the former needing a stack/path model, the latter a cardinality axiom.

---

## Phase 19 — The cardinality axiom: pigeonhole over a bounded domain  *(shipped)*

**The link the uninterpreted cardinality was missing.** `card(s)` (Phase 16) tracks only its per-mutation
deltas — it has no relationship to *which* elements a set holds, so `|s| <= n` for a set drawn from an
`n`-element domain was not derivable. `Sets.boundedBy(s, n)` supplies that relationship — the **pigeonhole** —
as a recognised contract predicate.

**The encoding — a faithful definition, not a trusted axiom.** `Sets.boundedBy(s, n)` means exactly
`s ⊆ [0, n)`, and the encoder lowers it to

```
card(s) <= n  ∧  (card(s) < n  ∨  ∀ i. 0 <= i < n ⟹ i ∈ s)
```

i.e. "bounded by the domain, and *full* (`card == n`) exactly when it covers `[0, n)`". Both pieces — the
cardinality comparison and the bounded membership universal — are already modelled, so this is a boolean
*definition* (sound in both assume and goal positions), not an axiom injected behind the user's back. The
runtime helper `Sets.boundedBy` evaluates the same predicate, so the groovy-contracts runtime check agrees.
`Encoder` recognises the `Sets.boundedBy(s, n)` call shape (like `Forall.range`) and emits the lowering, the
membership `select(s, i)` term serving as the universal's instantiation trigger.

From it the engine **derives** the two facts cardinality-driven search needs, neither previously provable:

- **FULL ⟹ MEMBER** — `Sets.boundedBy(s,n) ∧ s.size() == n ∧ 0 <= u < n ⊢ u ∈ s` (a full bounded set is the
  whole domain).
- **HOLE ⟹ NOT FULL** — `Sets.boundedBy(s,n) ∧ 0 <= u < n ∧ u ∉ s ⊢ s.size() < n` (a missing in-domain node
  means room remains) — exactly the coverage-branch fact a cardinality-terminating DFS needs.

Drop `Sets.boundedBy` and both refute: the uninterpreted size says nothing about membership.

**The honest boundary — why this does not, by itself, close whole-DFS unconditional coverage.**
`Sets.boundedBy` gives the pigeonhole *consequences*, but a recursive DFS must also **preserve** boundedness
across the add that *fills* the set — and proving `Sets.boundedBy(s ∪ {u}, n)` when `|s| = n-1` requires the
*converse* counting: `|s| = n-1 ∧ s ⊆ [0,n) ⟹ s is [0,n) minus exactly one element`, so the fresh in-domain
`u` is precisely that element. The definitional `Sets.boundedBy` does not yield "exact membership from exact
count". Closing it needs a **bounded-sum cardinality** `bcard(s, k) = Σ_{i<k} (i ∈ s ? 1 : 0)` with its
recursive defining axioms, plus the monotonicity/exact-count lemmas proved by induction (Phase 7) — at which
point `card(s)` over a domain *equals* `bcard(s, n)` and the counting closes. That bounded-sum cardinality is
the next set-reasoning increment; `Sets.boundedBy` is the usable pigeonhole layer above the uninterpreted
`card` and below it, and stands on its own (the `HOLE ⟹ NOT FULL` fact is the DFS coverage branch in
isolation).

---

## Phase 20 — Bounded-sum cardinality `bcount`: properties earned by induction  *(shipped)*

**The genuine count — and its foundational properties are *proved*, not axiomatised.** The bounded sum
`bcount(s, k) = Σ_{i<k} (i ∈ s ? 1 : 0)` is the real count of `s`'s members in `[0, k)` — the quantity
`Sets.boundedBy` (Phase 19) approximated and the uninterpreted `card` (Phase 16) had no handle on. The notable
part: it is *just an ordinary recursive Groovy method*, and its defining properties fall out of the framework's
own induction (`@Decreases` on `k`, the self-`@Ensures` as the inductive hypothesis, Phase 7) — there is no
built-in `bcount` and no trusted axiom.

```groovy
@Requires({ k >= 0 })
@Ensures({ 0 <= result && result <= k })        // the BOUND, by induction on k
@Decreases({ k })
static int bcount(Set<Integer> s, int k) {
    if (k == 0) return 0
    int rest = bcount(s, k - 1)                  // Assign-form call → the IH applies: 0 <= rest <= k-1
    return rest + ((k - 1) in s ? 1 : 0)         // (k-1) in s is a 0/1 membership ite
}
```

**Two foundational lemmas, both verified:**

- **Bound** — `0 <= bcount(s,k) <= k`. This is precisely the converse-counting *upper bound* the uninterpreted
  `card` could not provide (Phase 18's termination needed it; Phase 19's `Sets.boundedBy` could only *assume* it).
- **Full domain ⟹ count = k** — the same recursion under `@Requires({ (0..<k).every { it in s } })` proves
  `result == k`, tying the count to actual membership. The recursive call's precondition
  (`(0..<k-1).every { it in s }`) follows from the caller's over `[0, k)` by bounded-quantifier instantiation.

The bound is *earned*: a body that over-counts (`rest + 2`) refutes `result <= k`. No machinery was added —
this is the recursive-function induction (Phase 7) over the set membership and bounded quantifiers (Phases
9/16) already present, which is itself the point: the bounded-sum cardinality is *in reach of the existing
fragment*.

**What this unlocks, and what is still open for whole-DFS coverage.** `bcount` supplies the counting facts
`card`/`Sets.boundedBy` lacked. To finish wiring it into a DFS that proves *unconditional* coverage, two steps
remain, both needing **recursive-definition reasoning inside contracts** (so a `bcount(...)` term carries its
defining equation rather than reducing to an uninterpreted symbol):

- the **per-add law** — `bcount(s ∪ {u}, k) = bcount(s, k) + (0 <= u < k ∧ u ∉ s ? 1 : 0)` — the `bcount`
  analogue of the per-store `count` law (Phase 12), threading the count across a set mutation; and
- **cross-lemma use** — referencing `bcount` in one method's contract and discharging it from another's
  proved `@Ensures` (today a `bcount(s,k)` term *inside a contract* is modelled as an uninterpreted function,
  so its definition isn't visible across the lemma boundary).

With those, `card(s)` over a domain *equals* `bcount(s, n)`, the "`|s| = n-1` ⟹ exactly one hole" preservation
closes, and the cardinality-terminating DFS proves unconditional coverage. The foundational lemmas here are the
base that development builds on.

---

## Phase 21 — The bcount per-add law: `Sets.boundedCount` as a primitive  *(shipped)*

**Threading the count across a mutation — the first of the two steps Phase 20 flagged.** The recursive
`bcount` (Phase 20) *earns* its bound by induction, but a `bcount(...)` term inside another contract reduces to
an uninterpreted symbol (its definition isn't visible across the lemma boundary) and it cannot take `s ∪ {u}`
as an argument — so it cannot relate the count *before* and *after* a set mutation. `Sets.boundedCount(s, k)` is the
same bounded count exposed as a **primitive**, which can.

**The encoding — bound axiom + per-mutation law, the `count` machinery adapted.** `Sets.boundedCount(s, k)` is an
uninterpreted `(Set, Int) -> Int` (`setCount`, backed by Z3 `bcount$`). On first use of each term the encoder
asserts its **sound bound axiom** — `0 <= bcount`, `k >= 0 ⟹ bcount <= k`, `k <= 0 ⟹ bcount == 0` (all
theorems of "count of members in `[0,k)`", so asserting them keeps the symbol as strong as the count it
models). At every set mutation `s.add(u)` / `s.remove(u)`, for each `k` the postcondition or measure tracks
(harvested by `bcountKArgs`, mirroring `countValueArgs` for the Phase-12 `count` law), the **per-add law** is
asserted:

```
add:    bcount(s', k) = bcount(s, k) + (0 <= u < k ∧ u ∉ s ? 1 : 0)
remove: bcount(s', k) = bcount(s, k) - (0 <= u < k ∧ u ∈ s ? 1 : 0)
```

— the mutation changes the count only at slot `u`, and only when that slot lies in `[0, k)`. It rides the
existing per-store-law plumbing in `applySetMutation` (driven by the `currentBcountKExprs` set per discharge),
so it threads through both the postcondition check and the termination replay.

```groovy
@Requires({ 0 <= u && u < k && !(u in s) })
@Modifies({ this.s })
@Ensures({ Sets.boundedCount(s, k) == Sets.boundedCount(old.s, k) + 1 })   // verified
void put(int u, int k) { s.add(u) }
```

Verified, and sound on each edge: drop the freshness guard and the `+ 1` refutes; add an element *outside*
`[0, k)` and the count is provably unchanged (the law's domain guard); `remove` of a present in-domain element
decrements it; and the bound axiom rides the primitive (`0 <= Sets.boundedCount(s,k) <= k` for `k >= 0`).

**What remains for whole-DFS unconditional coverage.** One Phase-20 step is now done (the per-add law); the
other — **cross-lemma/definitional use** — is subsumed by giving `Sets.boundedCount` its **full-characterization**:
`Sets.boundedCount(s, k) == k ⟺ (0..<k).every { it ∈ s }` (the converse of Phase 20's "full ⟹ count = k", which the
per-add law's bound does not by itself supply). With it, the preservation argument closes — adding the fresh
in-domain `u` to a set whose count is `n-1` raises the count to `n`, which *forces* domain coverage, so
`Sets.boundedBy` is preserved across the filling add and the cardinality-terminating DFS proves unconditional
`start ∈ visited`. That full-characterization axiom (and then the frontier/stack invariant for *completeness*)
is the remaining work; the per-add law shipped here is its other half.

---

## Phase 22 — Full-characterization, and the end-to-end DFS unconditional coverage  *(shipped)*

**The capstone of the sets/maps/cardinality arc: a cardinality-terminating DFS proves it reaches the node it
is given — unconditionally.** The last axiom is the converse of Phase 20's *full ⇒ count*:

```
Sets.boundedCount(s, k) == k   ⟺   ∀ i. 0 <= i < k ⟹ i ∈ s        (count is full  ⟺  s covers [0, k))
```

Both directions are theorems of "count of members in `[0, k)`" (`k` members in `k` slots iff every slot is a
member), so the encoder asserts the iff for every `Sets.boundedCount(s, k)` term (in `setCountOf`, alongside the
bound axiom), the membership `select(s, i)` serving as the universal's trigger. The bounded-coverage `forall`
is factored (`domainCoverageForall`) and shared with `Sets.boundedBy`.

**Direct facts (verified):** `Sets.boundedCount(s,k) == k ∧ 0 <= u < k ⊢ u ∈ s` (full count forces every domain node
in); the reverse `(0..<k).every{it∈s} ⊢ Sets.boundedCount(s,k) == k`; and the domain bite — `Sets.boundedCount(s,k) == k`
says nothing about a `u` **outside** `[0, k)` (refuted).

**The end-to-end result.** A DFS over a functional graph (`next : Map<Node,Node>`) marking a `Set<Node>`,
terminated by the **set-cardinality** measure `n - Sets.boundedCount(visited, n)`, proves `u ∈ visited`
**unconditionally** — no fuel budget:

```groovy
@Requires({ 0 <= u && u < n && (0..<n).every { 0 <= next[it] && next[it] < n } })
@Modifies({ this.visited })
@Decreases({ n - Sets.boundedCount(visited, n) })
@Ensures({ (u in visited) && (0..<n).every { !(it in old.visited) || (it in visited) } })
void visit(int u) {
    if (!(u in visited) && Sets.boundedCount(visited, n) < n) { visited.add(u); visit(next[u]) }
}
```

How the obligations close: **termination** — the per-add law (Phase 21) makes `Sets.boundedCount(visited, n)`
strictly increase on the fresh in-domain add, so the measure drops by one and the bound axiom keeps it `>= 0`;
**coverage** — on the guard-false branch the model either has `u ∈ visited` already, or `Sets.boundedCount(visited,n)
>= n`, where the bound forces `== n` and the full-characterization then forces every domain node (`u`
included) into `visited`; on the guard-true branch `u` is added and the inductive hypothesis's monotonicity
carries it across the recursion's havoc. It composes every prior phase — sets, the map graph, induction,
caller-side set framing, bounded quantifiers, the per-add law, the full-characterization — into one result.
*(One wrinkle the build surfaced: `Sets.boundedCount` in a method **body** resolves to a `ClassExpression`
(`verification.Sets.boundedCount`), not the `VariableExpression`/`PropertyExpression` a re-parsed contract carries, so
the encoder's `Sets` recognition was widened to all three.)*

**What remains — completeness.** The proof covers the node *itself*, **not its successors**: `next[u] ∈
visited` refutes (a node visited earlier needn't have had its edge followed). That is *completeness* — every
reachable node is visited, the closure fixpoint — and it needs the DFS **frontier/stack invariant** ("`visited`
is closed under successors except on the recursion stack"), which is not a simple inductive set property: it
needs the stack modelled (a sequence/ghost) or an explicit inductive `IsPath` predicate with a least-fixed-point
argument. That is the one named, well-understood gap between here and a fully verified DFS; everything else —
termination, soundness, and unconditional coverage — is done.

---

## Phase 23 — A run at completeness: closure ⇒ reachable, and the obstacles  *(superseded by 24/25/26)*

**Completeness — *every reachable node is visited* — is the closure fixpoint.** It factors into two halves:
(b) "`visited` closed under `next` ⟹ every reachable node is visited", and (a) "the DFS *establishes* closure".

**What is proved here.** Closure as the bounded universal
`(0..<n).every { !(it in visited) || (next[it] in visited) }` lets the **one-step** consequence of (b) verify:
a closed set covers the successor of any visited node (`closure ∧ u ∈ visited ⊢ next[u] ∈ visited`) — the
inductive *step*, discharged by instantiating the closure universal.

**What was blocked, and where each block closed.** Attempting the full proof surfaced three coupled obstacles,
all since shipped:
- **Recursive definitions in contracts** — the inductive iteration over a `chain(u, d)` needed its defining
  equation visible across the lemma boundary. **Phase 25** lands this (shared symbol + bounded-depth eq); the
  full (b) half — *closure ⇒ EVERY reachable node visited* — now verifies.
- **DFS *establishing* closure** — a plain `mark` breaks closure (the new node's successor isn't visited yet),
  so the invariant is "closed-except-on-stack", needing a recursion-stack ghost. **Phase 26** delivers the
  frontier/stack invariant.
- **Call-site soundness** — the run found that `verifyCallSite` wasn't replaying intervening body mutations
  before discharging a callee's precondition, so a naive closure-threading DFS spuriously passed; recursive-call
  name conflation and missing early-return narrowing were coupled to the fix. **Phase 24** rebuilds the
  call-site path (fresh formals + full-path replay) and re-validates the recursive proofs — including the
  Phase-14 sort, whose recursive precondition had been passing vacuously.

With 24/25/26, every correctness property of DFS — termination, soundness, unconditional coverage, completeness
(both halves) — is machine-checked.

## Phase 24 — Call-site precondition soundness  *(shipped)*

**A soundness fix to the foundation — and the one that revealed a flagship had been resting on a vacuous
check.** The discharge of a callee's `@Requires` at a call site (`verifyCallSite`) was building its context
from the enclosing `@Requires` and the enclosing-`if` path facts only. It missed two things, both unsound:

- **Intervening body mutations weren't threaded.** A precondition over a *mutated* collection's contents was
  checked at the method's *entry* state, not the state at the call. (Surfaced by the Phase-23 closure-DFS:
  `visit(next[u])`'s closure precondition was checked against the *pre-`add`* `visited`, so a naive
  closure-threading DFS passed spuriously.)
- **Recursive-call name conflation.** The callee formal and the caller's same-named variable were the same SMT
  constant, so a self-call's formal binding asserted the garbled `u == next[u]` (or the inconsistent `n == n-1`
  for `sumUp(n-1)`) — checking the precondition in a corrupt/vacuous context. Many recursive call-site
  preconditions were therefore passing *vacuously*.

**The fix (three coupled parts):**

1. **Fresh callee formals.** The formal is a fresh symbol (`name#arg…`, kept out of displayed counterexamples
   by the `#` filter), pinned to the actual — distinct from any caller variable of the same name.
2. **Early-return path narrowing.** An `if (cond) return/throw` that *precedes* the call (not an enclosing
   `if`, so `PathFacts` misses it) contributes `¬cond` — the fact `sumUp(n-1)`/`bcount(s,k-1)` need
   (`n ≠ 0`/`k ≠ 0`) to show `n-1 ≥ 0`.
3. **Precise intervening-mutation replay.** The straight-line prefix (scalar/field assigns, array stores, map
   puts, set add/remove) is replayed into the context, and **the actual arguments are translated *after* the
   replay** — so `insert(m-1, a[m], v)` reads the post-swap `a[m]`. A non-straight-line prefix statement
   (an `if`/loop) soundly *havocs* what it might write.

**Outcome.** The closure-DFS precondition now correctly refutes; a `s.add(k); needs(k)` (where `needs` requires
`k ∈ s`) verifies *because* the add is threaded, and refutes without it; `sumUp`/`bcount` recursive
preconditions now discharge *soundly* (early-return narrowing) rather than vacuously.

**What it revealed — and restored — the Phase-14 sort.** The fix exposed that the capstone sort's recursive
precondition `insert(m-1, a[m], v)` had been passing **vacuously** (the `m == m-1` conflation). The *sound*
obligation needs the *transitive* bound `a[it] <= a[m-1]` (for all `it`) from *adjacent* sortedness — which
Z3 cannot get by e-matching (it times out; the trigger cliff). So the call-site rebuild also generalised the
preceding-call rule: **any** preceding call's `@Ensures` is now assumed in path order (sound *because* the
intervening mutations are threaded), not just the immediate predecessor. With that, a one-line **monotone-bound
lemma** (`maxBound`: every element of an adjacent-sorted prefix `[0,k]` is `<= a[k]`, proved by induction)
called *before* the swap supplies the transitive bound, and its `@Ensures` threads through the swap to the
recursive call — discharging the precondition *soundly*. The sort is fully verified again. This is also the
project's first worked **lemma-as-instantiation-hint** (roadmap Phase 8b): a hard quantifier proof made
tractable by a user lemma, no engine change beyond the call-site threading.

**Still not threaded (sound, documented):** a call nested as an *argument* of another call has no path step to
anchor the replay, so it falls back to the conservative entry-state context.

## Phase 25 — Recursive definitions in contracts: the defining-equation upgrade  *(shipped)*

**The piece that lets an inductive proof reason about a recursive function — and the last addition needed for
the *closure ⇒ every reachable node visited* half of completeness.** Phase 8a's symbolic unfolding *inlined* a
pure function's body at the call site; for a *recursive* function appearing in a contract this produced
different inlined terms at different fuel depths, so two occurrences (a goal `chain(u,d)` and the inductive
hypothesis's `chain(next[u],d-1)`) could not be equated, and the induction refuted.

**The fix — shared symbol + defining equation.** A contract-free same-class call `f(args)` is now translated to
a *shared* uninterpreted symbol `f#(args)` (so two occurrences are the same term by congruence), and its
**defining equation** `f#(args) == body[params↦args]` is asserted (sound by the function's purity). The body's
own recursive calls become `f#(deeper)` terms with their own equations, so the definition unfolds *as
equations* over shared symbols rather than as inlined terms.

**The depth subtlety that made it work.** A naïve shared total unfold budget fails on an inductive function
whose argument *drifts* (`chain(u,d) → chain(next[u],d-1) → chain(next[next[u]],d-2) → …`): the body expansion
drains the whole budget before the goal term is ever defined. So the budget is **per-term depth**, restored
after each top-level call — the goal and the hypothesis each get their equation independently. Depth (6) still
reaches base cases, so the concrete unfolds (`pow2(2) == 4`) keep working.

```groovy
int chain(int u, int d) { d <= 0 ? u : chain(next[u], d - 1) }   // the d-step successor
@Requires({ d >= 0 && 0 <= u && u < n && (u in visited) &&
            (0..<n).every { 0 <= next[it] && next[it] < n } &&
            (0..<n).every { !(it in visited) || (next[it] in visited) } })   // closure
@Ensures({ chain(u, d) in visited })
@Decreases({ d })
void propagate(int u, int d) { if (d > 0) propagate(next[u], d - 1) }       // verified
```

**Payoff.** Two things land: the **completeness (b) half** — closure ∧ `u ∈ visited` ⇒ every node reachable
from `u` is visited, by induction over `chain` (Phase 23's open inductive case) — and **`bcount` cross-lemma
use**: a single-expression `bcount(s,k)` referenced in a *separate* lemma's contract, whose bound
`0 <= bcount <= k` is proved by induction using the defining equation (the cross-lemma use the statement-form
Phase-20 `bcount` couldn't support; a wrong bound still refutes). It is also the bounded, in-grain form of
"recursive-definition reasoning" — no quantified function axioms, just ground defining equations to a fixed
depth, keeping clear of the trigger cliff.

## Phase 26 — The frontier/stack invariant: DFS establishes closure  *(shipped)*

**The last gap, and the capstone of the whole sets→maps→cardinality→completeness arc: a depth-first search
proven to leave its `visited` set *closed under the successor relation* — i.e. it reaches everything reachable.**
This is the deep half of DFS correctness, the one that needs the recursion *frontier* modelled, not just an
inductive set property.

**Why a plain invariant fails.** Mark-then-recurse marks `u` *before* recursing into `next[u]`, so right after
the mark `visited` is closed **except at `u`** (whose successor isn't visited yet); the recursion restores it.
A plain "closed under `next`" invariant therefore provably breaks on a single `mark` (Phase 23's boundary test).
The invariant DFS really maintains is **closed-except-on-stack**.

**The encoding — the stack as a `Set` ghost.** A second set field `onStack` is pushed (`onStack.add(u)`) before
the recursive call and popped (`onStack.remove(u)`) after. The invariant is
`∀ it ∈ [0,n). it ∈ visited ⟹ (it ∈ onStack ∨ next[it] ∈ visited)` — every visited node is on the stack or its
successor is visited. `visit` is proven to **maintain it and restore the stack** (the `@Ensures` includes a
pointwise *stack-restored* clause `(it in onStack) == (it in old.onStack)` and `onStack ⊆ visited`), so a
top-level `dfs` started with both sets empty leaves `onStack` empty — at which point the invariant *is* full
closure `∀ it. it ∈ visited ⟹ next[it] ∈ visited`.

```groovy
@Modifies({ [this.visited, this.onStack] })
@Decreases({ n - Sets.boundedCount(visited, n) })
void visit(int u) {
    if (!(u in visited) && Sets.boundedCount(visited, n) < n) {
        visited.add(u); onStack.add(u); visit(next[u]); onStack.remove(u)   // mark, push, recurse, pop
    }
}
// from empty visited + empty stack, one DFS ⇒ visited is closed under next:
@Ensures({ (0..<n).every { !(it in visited) || (next[it] in visited) } })
void dfs(int start) { visit(start) }
```

**How the obligations close.** The proof composes *everything*: the **pop** after the recursive call is threaded
by Phase 24's call-site/mutation machinery; the recursion **havocs both sets and reframes** them from `visit`'s
`@Ensures` (sound `@Modifies` over two sets); the **stack-restored** clause lets the pop cancel the push
(`u ∉ onStack` follows from `onStack ⊆ visited` and `u ∉ visited`); `u ∈ visited` (needed so the recursion
covers `next[u]` in the invariant's `it == u` case) rides the **`Sets.boundedCount` full-characterization** (Phase 22)
on the "set full" branch; and termination is the **set-cardinality measure** (Phase 16). No new engine
machinery — it is the entire stack of phases 16–25 brought to bear on one proof.

**Cost.** This is the heaviest proof in the suite — several quantifiers over two mutated sets with map-indexed
bodies, plus the defining-equation overhead (Phase 25). It stays within the per-VC timeout (no UNKNOWNs), but
the suite's wall-clock grew noticeably; a tighter unfold depth, VC caching, or per-VC tactic selection (the
cross-cutting compilation-slowdown item) is the natural optimisation now that the capability is proven.

**The arc is complete.** Termination (16/17), soundness + bounded progress (18), the cardinality axiom (19),
bounded-sum cardinality and its laws (20–22), unconditional coverage (22), recursive-defs in contracts (25),
call-site soundness (24), and now closure (26): **a depth-first search over a cyclic graph, every correctness
property machine-checked, by induction, with no loops** — the goal this whole line of work was aimed at.

## Phase 27 — Non-Int element domains: `String` and `Enum` in sets, maps, lists  *(shipped)*

**Real-world Groovy uses string keys and enum-typed fields; the engine was Int-only until now.** Sets,
maps, and lists modelled their elements as `Int` — fine for the DFS over a finite node domain that
Phases 16–22 built up, but `Set<String>`, `Map<String, V>`, `List<Color>` (the everyday shapes) were
out of fragment. This phase lifts the element-sort assumption: any literal of a recognised non-Int
element type lowers to a constant of that type's Z3 uninterpreted sort, and all the existing
operations (`contains`/`add`/`size`/`put`/`get`/subscript read+write) thread through that sort
untouched.

**The encoding — uninterpreted sorts plus pairwise distinct.** Each non-Int element type maps to a Z3
uninterpreted sort (`String!Sort`, `Color!Sort`, …), declared once per name and shared across the
session. A literal (`"admin"`, `Color.RED`) mints a constant of that sort, interned by literal text;
on each new mint, the constant is asserted distinct from every previously-minted literal of the same
sort. So `s.contains("admin")` and `s.contains("guest")` resolve to two different `(select s _)`
queries — `contains("admin")` doesn't entail `contains("guest")` (refutes, with the
counterexample-as-Groovy-literal renderer showing `f("admin")` in `fails on:`). Two enums with the
same source-level simple name in different outer classes collapse into one sort — accepted limit.

**Cross-AST-shape consistency.** A contract closure is re-parsed from text, so `Color.RED` arrives as
`PropertyExpression(VariableExpression("Color"), "RED")`. The method body is post-resolution, so the
same `Color.RED` arrives as `PropertyExpression(ClassExpression(C$Color), "RED")` — the nested-enum
binary name `C$Color` diverges from the source-level `Color`. Two normalisations make them converge:
the enum sort name is the simple name with any `$`-prefix stripped (so `C$Color` → `Color`), and the
literal-key interning uses the property name alone (`"RED"`) — the expected sort already
disambiguates cross-enum (`Suit.RED` vs `Color.RED` reach different sorts).

**`Set<E>` / `Map<K,V>` / `List<E>` routing** — `VerifyChecker` extracts the element/key/value types
from declared generics in `beforeVisitMethod` (`collectSetElementTypes` / `collectMapTypes` /
`collectListElementTypes` / `collectScalarTypes`) and hands them to the `Encoder`. The encoder's
array allocator `arrayFor` now dispatches on `[keySort, valueSort]` — a map value array becomes
`Array KeySort -> ValueSort`, a non-Int list `Array Int -> ElemSort`. The set characteristic array
likewise: `Array ElemSort -> Int`. Per-element-sort `card$T` / `bcount$T` functions are declared
lazily on the backend so cardinality works for `Set<String>` the same way it does for `Set<Integer>`.

**`Sets.boundedBy(s, n)` / `Sets.boundedCount(s, k)` are Int-only here, generalised in Phase 29.** Both
originally depended on the `[0, n)` Int-domain structure (the lowering is a bounded membership
universal over Int indices). For non-Int element sets they returned null and the standard "outside
fragment" skip diagnostic fired. Phase 29 below generalises them to enum-element sets when
`n`/`k` matches the enum's domain size — the bounded-universal coverage becomes a finite
conjunction over the enum's constants. The String case still skips (strings have no finite
domain).

**Counterexample rendering.** A refuting String/Enum parameter's model value is recovered by
checking equality-under-the-model against each interned literal of the same sort (Z3 may assign a
synthetic uninterpreted-sort constant instead of one of our minted ones — string-name matching
alone misses these cases). The repro is rendered as a Groovy literal: `f("admin")` for String,
`f(Color.RED)` for Enum.

```groovy
class C {
    enum Color { RED, BLUE, GREEN }
    Set<Color> palette
    @Requires({ !(Color.RED in palette) })
    @Modifies({ this.palette })
    @Ensures({ palette.size() == old.palette.size() + 1 })
    void useRed() { palette.add(Color.RED) }
}
```

Verifies. Drop the freshness `@Requires` and the `+ 1` refutes with `fails on: useRed()` — a
no-op-add is one model.

**Known limits.** Set algebra (union/intersection/subset) stays a loud skip (it needs an unbounded
`∀x. x∈s ⇒ x∈t`); element-domain mixing (e.g. `Map<K, Set<V>>` nesting) is not yet wired; non-Int
element domains other than String and Enum (records, value classes, arbitrary objects) fall through
to the default-Int path and emit a skip. None of these need new theory — just additional
collect/dispatch wiring on the same pattern. The `Sets.boundedBy`/`Sets.boundedCount` Int-only restriction
from this phase was lifted in Phase 29 for the enum case.

## Phase 28 — `EnumClass.values().length` folds to a ground int  *(shipped)*

**A small piece of normalisation that unlocks ground state-coverage proofs.** `Color.values().length`
(and the equivalent `.size()` method form) is a syntactically uniform way to spell an enum's domain
size, but it reached the encoder as a `MethodCallExpression` whose return type isn't modelled — so
contracts like `@Requires({ k < Color.values().length })` skipped as outside fragment. This phase
folds the expression to its literal value at translate time, the same accelerator pattern as
Phase 8a's closed-constant evaluation, scoped narrowly to the one shape.

**How it works.** Both AST shapes are recognised:

- **Post-resolution body**: `PropertyExpression(MethodCallExpression(ClassExpression(Color),
  "values", []), "length")` — the encoder has direct access to the `ClassNode`, counts enum
  constants by walking the type's fields and filtering on the JVM {@code ACC_ENUM} modifier bit
  (`0x4000`), emits an `intLit`.
- **Re-parsed contract**: `PropertyExpression(MethodCallExpression(VariableExpression("Color"),
  "values", []), "length")` — the receiver name has no resolved type, so `VerifyChecker` walks the
  declaring class's module in `beforeVisitMethod`, builds a `Map<String, Integer>` of enum simple
  names → constant counts (both the source-level `Color` key and the inner-class-stripped form for
  nested enums), and hands it to the encoder.

The `ACC_ENUM` filter is the load-bearing detail: Groovy synthesises additional same-typed
`MIN_VALUE` and `MAX_VALUE` fields on every enum, so counting "static fields whose declared type
matches the enum class" would inflate a 3-constant `Color` to 5. The JVM modifier flag is set only
on real enum constants.

```groovy
class C {
    enum Color { RED, BLUE, GREEN }
    @Ensures({ result == 3 })
    static int numColors() { Color.values().length }                          // verifies
    @Requires({ k < Color.values().length })
    @Ensures({ k <= 2 })
    static int safe(int k) { k }                                              // verifies
    @Ensures({ result == 4 })                                                  // refutes
    static int wrong() { Color.values().length }
}
```

**What it unlocks (and what it doesn't).** The folded literal is usable anywhere an `int` literal is
— upper bound of a bounded range (`(0..<Color.values().length).every { … }`), `Sets.boundedBy(s, n)`
over an Int-element set, ground constraint in a postcondition. Phase 29 below additionally uses
the folded count to enable `Sets.boundedBy` / `Sets.boundedCount` over a `Set<Color>` (the FSM
completeness shape). What this phase *doesn't* give on its own: recognition of enums defined in
*other* modules (only the current module's enums are walked). Cross-module enum support would
extend `collectEnumDomainSizes` to consult the compilation unit's classloader; the foundation is
there.

## Phase 29 — `Sets.boundedBy` / `Sets.boundedCount` generalised to enum-element sets  *(shipped)*

**The "FSM proves every state handled" example, with the natural `Set<State>` spelling.** Phase 27
step 8 honestly skipped `Sets.boundedBy` / `Sets.boundedCount` on non-Int element sets — the bounded
universal `∀ i. 0<=i<n ⟹ i ∈ s` is meaningless when `s`'s elements aren't Int. For enums, the
finite domain gives a clean substitute: enumerate the constants, write the coverage as a finite
conjunction. This phase wires that, and lets the natural FSM completeness proof verify directly.

**The encoding.** On first mint of an enum-element set (`setFor` returning a fresh handle), two
facts the finite enum domain gives are asserted unconditionally:

- **Pigeonhole**: `card(s) <= N` where N is the enum's constant count.
- **Full-coverage iff**: `card(s) == N ⟺ c1 ∈ s ∧ … ∧ cN ∈ s` — finite conjunction over the
  enum's constants (the same interned literals Phase 27 already mints).

`Sets.boundedBy(s, n)` and `Sets.boundedCount(s, k)` then dispatch on element sort. For Int: the existing
Phase 19 / 22 machinery (bounded universal). For enum, when `n`/`k` folds to the enum's domain
size (via Phase 28's `EnumClass.values().length` recognition or a literal): `Sets.boundedBy(s, n)`
lowers to `card(s) <= n ∧ (card(s) < n ∨ finite-conjunction)`, and `Sets.boundedCount(s, k)` aliases to
`card(s)` (no partial-domain ordering on an enum, so the only meaningful count is the whole-set
size). Non-matching `n`/`k` skips with the standard "outside fragment" diagnostic — the
restriction is the partial-domain ambiguity, not the element sort.

```groovy
class FSM {
    enum State { IDLE, RUNNING, DONE }
    Set<State> handled
    @Requires({ Sets.boundedCount(handled, State.values().length) == State.values().length })
    @Ensures({ State.IDLE in handled && State.RUNNING in handled && State.DONE in handled })
    boolean allHandled() { true }
}
```

Verifies. `State.values().length` folds to `3` (Phase 28), `Sets.boundedCount(handled, 3)` aliases to
`card(handled)` (Phase 29), the iff axiom `card(handled) == 3 ⟺ IDLE ∈ handled ∧ RUNNING ∈ handled
∧ DONE ∈ handled` was asserted at the set's first use, so `@Requires` ⟹ `@Ensures`. Drop the
`@Requires` and the postcondition rightly refutes — partial coverage can't prove every state.

**Pigeonhole is automatic.** A method whose postcondition is `s.size() <= 3` over a `Set<State>`
verifies *without* requiring `Sets.boundedBy` — the bound was asserted at setFor time. Same for the
implication "this set has at most as many elements as its enum has constants" anywhere it's
needed.

**Known limits.** Set union/intersection (constructive new-set operations), nested element domains
(`Map<K, Set<V>>`), and non-enum non-Int element domains (String, records, …) all remain as they
were after Phase 27. Subset (`s.containsAll(t)`) over enum-element sets is added in Phase 30 below;
the Int-element subset case still needs bounded-domain context plumbing.

## Phase 30 — Subset reasoning: `s.containsAll(t)` over enum-element sets  *(shipped)*

**The canonical authorization predicate, machine-checked.** `granted.containsAll(required)`
expresses subset directly — "every role required is among the granted" — and is the building block
for set equality, ACL checks, FSM coverage transfer, and the membership half of union/intersection
later. This phase adds it for enum-element sets, where the finite domain gives a clean lowering
without any unbounded universal.

**The encoding.** `s.containsAll(t)` lowers to the finite conjunction
`(c1 ∈ t ⟹ c1 ∈ s) ∧ … ∧ (cN ∈ t ⟹ cN ∈ s)` over the enum's constants — the same shape Phase 29
uses for full-coverage, with implication instead of bare membership. Reflexivity, transitivity, and
the "add preserves subset" pattern all fall out of the conjunction structure under Z3's
propositional reasoning; no quantifier needed.

```groovy
class C {
    enum Role { ADMIN, USER, GUEST }
    @Requires({ granted.containsAll(required) && Role.ADMIN in required })
    @Ensures({ Role.ADMIN in granted })                         // verifies — subset entails transfer
    static int check(Set<Role> granted, Set<Role> required) { 0 }
}
```

Drop the `containsAll` precondition and the `@Ensures` refutes — without subset, membership in
`required` says nothing about `granted`.

**Enhancement: empty iff.** The Phase-29 enum-set axioms covered `card(s) == N ⟺ full coverage`
but not the dual at the empty endpoint. Phase 30 adds the third axiom:
{@code card(s) == 0 ⟺ ¬c1 ∈ s ∧ … ∧ ¬cN ∈ s}, asserted at every enum set's first mint
alongside the pigeonhole and full-coverage iff. So `s.size() == 0` now implies every constant is
absent — letting empty-subset claims (`s.containsAll(empty)`) verify by vacuous implication, and
"this method clears the set" postconditions imply non-membership of every constant.

**Known limits.** Phase 31 (below) lifts the Int-element subset restriction by threading a
registered `Sets.boundedBy(t, n)` into the subset lowering. Phase 32 adds `s.equals(t)` as a
two-direction composition over the same subset primitive. Set union/intersection remain
deferred — they're *constructive* (mint a new set with a derived membership predicate) and need
a different shape than the pure-predicate lowering here.

## Phase 31 — Int-element subset via bounded-domain context  *(shipped)*

**Closes the Int-side of subset.** Phase 30 lowered `s.containsAll(t)` over enum-element sets to a
finite conjunction — the finite domain made it ground. For Int-element sets the user has to
supply the domain via a `Sets.boundedBy(t, n)` clause; once they do, the subset lowering becomes
the natural bounded universal `∀i. 0 <= i < n ⟹ (i ∈ t ⟹ i ∈ s)`. Same shape Phase 19 / 22
already lean on, applied to a new predicate.

**The plumbing — `intSubsetBounds`.** A per-encoder map (set-key → bound handle) is populated as
a side-effect of `translateSetsBounded`'s Int branch: when `Sets.boundedBy(t, n)` translates, it
records `t`'s key with `n`'s Z3 handle. A later `s.containsAll(t)` on Int sets consults this map;
if a bound is registered, it emits the bounded universal with `(select t i)` and `(select s i)`
as triggers. Without a bound (`Sets.boundedBy` not in scope, or `containsAll` translated *before*
the bound clause in L-to-R AST order), the lowering returns null and the standard "outside
fragment" skip diagnostic fires.

```groovy
class C {
    @Requires({ Sets.boundedBy(required, n) && granted.containsAll(required) &&
                0 <= u && u < n && u in required })
    @Ensures({ u in granted })
    static int check(Set<Integer> granted, Set<Integer> required, int n, int u) { 0 }
}
```

Verifies. Reflexivity and transitivity over Int sets (with a shared bound) both go through the
same way enum subset did in Phase 30. The bound *must* be on the subset operand (`t`), not the
superset — the universal needs to range over `t`'s candidate elements.

**Ordering caveat.** Because the bound is populated by side-effect when `Sets.boundedBy(t, n)`
translates, a contract written `@Requires({ a.containsAll(t) && Sets.boundedBy(t, n) })` (subset
first, bound after) skips — at the time `containsAll` is translated, the bound isn't yet
registered. Writing the bound first (`Sets.boundedBy(t, n) && a.containsAll(t)`) works. Not a
soundness issue (skip is honest), but a UX quirk worth knowing.

## Phase 32 — `m.containsValue(v)` for enum-keyed maps + `s.equals(t)` for sets  *(shipped)*

**Two small completions on top of the subset machinery.** `m.containsValue(v)` and `s.equals(t)`
were the next items in the deferred set/map algebra row; both are small enough to ship together,
both compose with what's already there.

**32a — `m.containsValue(v)` for enum-keyed maps.** The existential mirror of Phase 30's finite
conjunction: lower to `(m[c_1] == v) ∨ … ∨ (m[c_N] == v)` over the enum's key constants. The
value is translated in the map's value sort (Int / String / Enum all work). Int-keyed and
String-keyed maps skip honestly — no finite key domain to enumerate.

```groovy
class Registry {
    enum State { IDLE, RUNNING, DONE }
    Map<State, Integer> errorCodes
    @Requires({ errorCodes[State.RUNNING] == 42 })
    @Ensures({ errorCodes.containsValue(42) })
    boolean hasError42() { errorCodes.containsValue(42) }
}
```

Verifies: the key-pinned `[State.RUNNING] == 42` makes the `RUNNING` disjunct true, and the
disjunction holds. Drop the `@Requires` and the postcondition rightly refutes.

**32b — `s.equals(t)` for sets, by subset composition.** Pure composition, no new theory:
`s.equals(t) ≡ s.containsAll(t) ∧ t.containsAll(s)`. Reuses the Phase 30/31 subset lowering in
both directions. Works for any element sort the subset path handles (enum: always; Int: with
mutual `Sets.boundedBy` bounds). Both directions need to translate; if either skips, equals does too.

Reflexivity (`s.equals(s)`) is automatic. The diagnostic-form alternative to writing `s == t`
directly — which would lower to Z3's array-equality predicate (an unbounded universal on the
characteristic functions). The method-form path gives the user a propositionally-decomposed
alternative Z3 reasons about as ground facts.

**Known limits.** Int-keyed map `containsValue` would need a key-set bound (similar to Phase 31's
`intSubsetBounds`) and isn't yet wired. `s.equals(t)` for Int sets without mutual bounds skips.

## Phase 33 — Inline set union / intersection  *(shipped)*

**The last set-algebra slice the deferred row called out, in its tractable form.** A user writing
`(a + b).contains(x)` or `a.intersect(b).containsAll(u)` in a contract gets the natural lowering
without the encoder having to mint a new set handle for the binary operation's result. The result
is treated as a *predicate context* — every method called on it lowers lazily by chaining through
to the operands.

**The encoding — lazy at the use site.** Recognised receiver shapes:
- {@code (s + t)} — Groovy's {@code Set.plus} binary expression (BinaryExpression with PLUS op).
- {@code s.intersect(t)} — Groovy GDK method-form intersection (MethodCallExpression).

Both must be two known set names with matching element sort; otherwise honest skip. Methods on
the result lower:
- {@code .contains(x)}: union → {@code x ∈ s ∨ x ∈ t}; intersection → {@code x ∈ s ∧ x ∈ t}.
- {@code .containsAll(u)} (enum element sort): finite conjunction over the enum's constants —
  {@code (c ∈ u ⟹ c ∈ s ∨ c ∈ t)} for union, {@code (c ∈ u ⟹ c ∈ s ∧ c ∈ t)} for intersection.
- The {@code x in (s + t)} / {@code x !in s.intersect(t)} membership operator forms route through
  the same lowering — mirror of the method-form path.

```groovy
class C {
    enum Role { ADMIN, USER, GUEST }
    @Requires({ a.containsAll(u) })                   // a covers u
    @Ensures({ (a + b).containsAll(u) })              // the union covers u — adding b only helps
    static int f(Set<Role> a, Set<Role> b, Set<Role> u) { 0 }
}
```

Verifies via the finite conjunction. Drop the @Requires and the @Ensures rightly refutes — without
a covering u from either operand, the union claim doesn't hold.

**Known limits.**

- **Materialised set assignment** — `Set<X> u = a + b` followed by treating `u` as a fresh
  first-class set with its own size/membership — is still out. Needs a constructive set-handle
  mint with the membership iff axiom; bigger phase.
- **`.size()` on a union/intersection** — out of scope. Needs inclusion-exclusion
  `|s ∪ t| = |s| + |t| − |s ∩ t|` to be useful; the uninterpreted `card` has no axiom relating
  cards of derived sets. Skip honestly.
- **Int-element `containsAll` on a binop receiver** — would extend Phase 31's
  `intSubsetBounds` plumbing to recognise a bound on the subset operand of the binop expression;
  not yet wired. Enum is the only path today for the `containsAll`-on-binop case.

## Phase 34 — VC cache  *(shipped)*

**The first pure-engineering phase.** No new capability, no new contract surface — a *cross-cutting
risk* the project flagged from the start ("compilation slowdown — Z3 calls take 10–100 ms each;
mitigations: cache VCs by `(signature, path-condition hash)`"). The mitigation is now in.

**The encoding.** Two VC checks built from the same set of asserted Z3 expressions — compared
structurally via {@code Expr.toString()}, with the asserted-set sorted to a canonical order, and
prefixed with the solver timeout to keep hard-UNKNOWN results from leaking across configurations
— must produce the same {@code CheckResult}, by Z3's determinism. {@code Z3Backend} now keeps a
process-wide {@code ConcurrentHashMap<String, CheckResult>} consulted at the top of
{@code Z3Session.check()}: hit → return immediately; miss → solve, cache, return.

```groovy
@Override
CheckResult check() {
    String key = vcKey()
    CheckResult cached = Z3Backend.vcCache.get(key)
    if (cached != null) { Z3Backend.recordVCCacheHit(); return cached }
    Z3Backend.recordVCCacheMiss()
    CheckResult result = computeCheck()
    Z3Backend.vcCache.put(key, result)
    return result
}
```

**Soundness.** A cached {@code CheckResult} carries only {@code String} → {@code Long} /
{@code String} maps — no Z3 handles — so the counterexample re-renders correctly in any future
session that declared the same source-level names. Sorts are differentiable inside the assertion
text (an {@code Int} {@code n} and a {@code String} {@code n} would always appear inside
operations that disambiguate them; their {@code toString} differs), so cross-sort name aliasing
can't cause unsound conflation.

**The result.** Test suite drops from **31.5 s to 25.8 s** (–18 %) at 253 cases, with **94 hits
/ 359 misses ≈ 20.8 % hit rate** — the misses are the ~1.4 distinct VCs each test contributes to
the cache for the first time; the hits are the precondition / bounds / null check obligations
that recur across the suite. Set {@code VERIFY_CACHE_STATS=1} to surface the counters.

**Known limits.** Two VCs that are *logically* equivalent but *syntactically* different (e.g.
{@code a + b} vs {@code b + a}, {@code a ∧ b} vs {@code b ∧ a} inside a single conjunct) miss the
cache. A canonicaliser would lift hit rates further at the cost of an extra normalisation pass
per assertion; not pursued today. The cache is also process-wide rather than persisted — each
{@code ./gradlew verify} rebuilds it from scratch. Persistent caching keyed on the project's
class-file digests is a much larger phase (file-system layout, invalidation on dependency
upgrades, cross-machine reproducibility) and the in-memory wins were already worthwhile alone.

## Phase 35 — Materialised set ops  *(shipped)*

**Lifts Phase 33's predicate form to a value form.** Phase 33 lowered {@code (a + b).contains(x)}
and friends *at the use site* — no new set handle minted, the binop stayed a predicate context.
Phase 35 takes the next step: an *assignment* whose RHS is a set union or intersection mints a
fresh set handle for the left-hand side, with the full per-element membership iff relating it to
its operands. Every existing set capability — subset, equals, cardinality update laws on
subsequent mutations, the enum-domain pigeonhole / full-coverage iff / empty iff axioms — picks
up the new local automatically.

**Detection.** The body's {@code DeclarationExpression} already becomes an {@code Assign} step in
{@code BodyEncoder}. The new branch in {@code VerifyChecker}'s {@code Assign} handler runs
{@code Encoder.tryMaterialiseSetBinopAssign(name, rhs)} *before* the int-SSA path. The encoder
reuses Phase 33's {@code setBinopFor} (now also unwrapping an outer {@code CastExpression}, so
{@code Set<Role> u = a.intersect(b) as Set<Role>} — needed because Groovy's GDK
{@code Collection.intersect} returns {@code Collection}) — and on a match commits:

```groovy
setElementTypes.put(name, binop.elemType)   // u becomes a "known set" downstream
Object uH = setFor(name)                     // mint the handle (auto-asserts enum-domain axioms)
for (String c : enumConstantNames(elemType)) {
    Object inU = member(uH, lit(c))
    Object inA = member(setFor(binop.leftKey),  lit(c))
    Object inB = member(setFor(binop.rightKey), lit(c))
    Object rhs = binop.isUnion ? or([inA, inB]) : and([inA, inB])
    session.assertExpr(eq(inU, rhs))         // c ∈ u ⟺ c ∈ a OP c ∈ b
}
```

**Why this composes for free.** Because {@code u} is registered in {@code setElementTypes}, the
encoder's existing {@code setFor(name)} machinery — which auto-asserts pigeonhole
({@code card(u) ≤ N}), full-coverage iff, and empty iff for enum-element sets — fires on the
mint. Everything downstream that already reasons about set parameters and fields
({@code u.containsAll(z)}, {@code u.equals(v)}, {@code Sets.boundedCount(u, k)}) now reasons
about {@code u} the same way; there's no special "materialised set" path elsewhere in the
codebase. The membership iff is the *only* extra fact Phase 35 emits.

```groovy
class C {
    enum Role { ADMIN, USER, GUEST }
    @Requires({ Role.ADMIN in a })
    @Ensures({ result == 1 })
    static int f(Set<Role> a, Set<Role> b) {
        Set<Role> u = a + b
        Role.ADMIN in u ? 1 : 0     // provable: the iff makes ADMIN ∈ u true under @Requires
    }
}
```

Verifies. Drop the @Requires and the else-branch becomes feasible (no constraint forces ADMIN
into either operand), so {@code result == 1} rightly refutes.

**Known limits.**

- **Enum-element domain only.** Int-element and uninterpreted-sort set binops would need an
  unbounded universal with trigger on {@code select(u, x)} — pulls in quantifier reasoning for
  every downstream membership query, deferred (parallels Phase 33's Int-binop {@code containsAll}
  known limit).
- **First assignment only.** A reassignment {@code u = a + c} after the original
  {@code u = a + b} isn't supported — the materialise path is the *declaration* form. Groovy
  rarely reassigns local sets, so this hasn't hurt in practice.
- **Cast handling stops at the outer expression.** A nested cast inside one of the operands —
  e.g. {@code (a as Set) + b} — works because the outer expression is the {@code +} binop, but a
  cast wrapping the whole thing on the *right* hand side is the only cast we unwrap. Reasonable
  given the GDK signature it's there to satisfy.
- **No inclusion-exclusion.** {@code card(u) = card(a) + card(b) − card(a ∩ b)} for a union is
  still out (Phase 33's known limit on {@code .size()} of a binop). The enum-domain pigeonhole
  upper bound + full-coverage iff usually suffice for FSM-shape proofs that care about
  *coverage*, not exact size.

## Phase 36 — Map&lt;K, Set&lt;V&gt;&gt; nesting (read-only)  *(shipped)*

**The final row-2 deferred item: nested element domains.** A {@code Map<K, Set<V>>} reads as one
SMT array whose *value sort is itself an array sort* — the inner set's characteristic function.
Z3's array theory has always supported this: {@code Array<K, Array<V, Int>>} is a perfectly
ordinary sort. What was missing was the Groovy/encoder plumbing: until Phase 36, the value-type
extraction in {@code twoGenericsOrInt} returned {@code Set} (the raw outer-level type), the
encoder defaulted to {@code Int} as the value sort, and any subsequent {@code m[k].contains(x)}
hit "outside fragment" because {@code m[k]} was being typed as a scalar.

**The encoding — value sort lifted to an array.** A new {@code SmtSession.arraySort(key, val)}
returns a Z3 sort *without* minting a constant (the existing {@code arrayVarOfSort} mints; we
need just the sort to compose nested sorts). Two new collect passes:

```groovy
// VerifyChecker
currentNestedSetValueTypes = collectNestedSetValueTypes(node)   // Map<String, ClassNode>: mapName → V
```

drive a small change in {@code Encoder.mapValueSort}:

```groovy
ClassNode nestedElem = nestedSetValueTypes.get(name)
if (nestedElem != null) {
    return session.arraySort(sortFor(nestedElem), session.intSort())
}
// existing: sortFor(pair[1])
```

so the map's value array now mints as {@code Array<K, Array<V, Int>>} — and {@code select(map, k)}
yields a transient inner-set term that the existing {@code member}/{@code select} machinery
already handles.

**The dispatch.** A new {@code nestedSetReceiverFor(Expression)} recognises {@code m[k]} for a
known nested-set map, resolving it to {@code select(mapValsFor(m), translatedKey)} packaged with
the inner element sort and {@link ClassNode}. Both {@link #translateMethodCall} (for
{@code .contains}/{@code .containsAll}) and {@link #translateBinary} (for the {@code in} /
{@code !in} operator) consult it before falling through to the existing receiver shapes:

```groovy
// translateMethodCall
NestedSetReceiver nr = nestedSetReceiverFor(recv)
if (nr != null) {
    if (m == 'contains') return member(nr.innerSet, translateInSort(args.get(0), nr.innerElemSort))
    if (m == 'containsAll') return translateNestedContainsAll(nr, args.get(0))
    return null
}
```

{@code translateNestedContainsAll} is a finite conjunction over V's enum constants — structurally
the same shape as Phase 30's {@link #translateContainsAll}, but operating on a transient inner-set
term instead of a named handle.

```groovy
class C {
    enum Role { ADMIN, USER, GUEST }
    @Requires({ m[Role.ADMIN].containsAll(s) && Role.USER in s })
    @Ensures({ Role.USER in m[Role.ADMIN] })
    static int f(Map<Role, Set<Role>> m, Set<Role> s) { 0 }
}
```

Verifies. The finite conjunction over {@code Role} constants closes the gap between
"{@code m[ADMIN]} covers {@code s}" and "{@code USER} is in {@code m[ADMIN]}" once
{@code USER ∈ s} is in scope.

**Known limits.**

- **Read-only.** {@code m[k] = newSet} (replacing the whole set at a key) and {@code m[k].add(x)}
  (in-place inner-set mutation) are out. The former needs the existing map-put plumbing to thread
  array-valued stores; the latter needs SSA on a *transient* inner handle plus the per-mutation
  cardinality law. Together they're a separate ~3-day phase.
- **No `m[k].size()`.** Cardinality of a transient inner set would need to mint a named handle on
  the fly so {@link SmtSession#setCard} could apply — out of scope; skips honestly.
- **`m[k].containsAll(s)` over Int-element inner sets.** Would need Phase 31's
  {@code intSubsetBounds} applied to a transient receiver — parallels the Phase-33-known-limit
  for Int-binop {@code containsAll}; not yet wired. Enum-V inner sets are the only path today.
- **One layer of nesting.** {@code Map<K1, Map<K2, Set<V>>>} (three-level nesting) isn't
  recognised: {@code collectNestedSetValueTypes} introspects only one level deep. Genuinely
  rare; not pursued.

## Phase 37 — List element nullability  *(shipped)*

**The row-1 nullability slice.** Until Phase 37, {@code xs[i].method()} and
{@code xs.get(i).method()} silently passed — the implicit-NPE pass recognised only *named*
receivers ({@code recv.method()}), so an unguarded dereference into a list element was outside
the obligation set. Phase 37 closes that: every indexed-element dereference is now an
unconditional obligation against a per-element nullity oracle, discharged by a contract guard
or an in-body {@code if} check.

**The encoding.** A new
{@code Encoder.elementNullityFor(name)} returns a lazily-minted {@code Array<Int, Int>} keyed
{@code <name>$nullElem} — the now-familiar 1/0 characteristic-array shape that {@link Sets} and
the map key-set already use. The lowering is symmetric on both faces:

- **Contract face.** {@code xs[i] == null} / {@code null == xs[i]} (and {@code xs.get(i) == null}
  shape) translate to {@code select(xs$nullElem, i) == 1}; the {@code !=} mirrors negate. So a
  {@code @Requires({ xs[i] != null })} pins {@code select(xs$nullElem, i) == 0} in the path
  context.
- **Body face.** The {@code ObligationCollector} now emits a {@code DerefSite} for
  {@code xs[i].method()} / {@code xs.get(i).method()} shapes (recognised by
  {@code Encoder.indexedAccessTarget}, the same helper the contract face uses) carrying the
  index expression alongside. The discharge asserts the negation
  ({@code select(xs$nullElem, i) == 1}) and Z3 returns SAT exactly when the element *can* be
  null on this path — refuted, with the counterexample rendered as e.g. {@code fails on: f([null])}.

```groovy
class C {
    @Requires({ xs.size() > 0 && xs[0] != null })
    static int f(List<String> xs) { xs[0].length() }       // verifies
}
class D {
    @Requires({ xs.size() > 1 && xs[0] != null })
    static int f(List<String> xs) { xs[1].length() }       // refutes — guard was on index 0
}
```

The wrong-index refutation drops out for free: the contract pins
{@code select(xs$nullElem, 0) == 0}, but the body's obligation is about
{@code select(xs$nullElem, 1)}, which Z3 is free to assign 1.

**Annotation plumbing.** {@code collectNonNullElementContainers} reads the standard NullChecker-
shape simple-name set ({@code NonNull}, {@code NotNull}, {@code Nonnull},
{@code MonotonicNonNull}) off the element generic and the array component type, suppressing the
implicit obligation for declared-non-null containers — *if* Groovy's AST preserves the
annotation at the read position. In current Groovy 6.0.0-SNAPSHOT, type-use annotations on
generics ({@code List<@NonNull String>}) aren't reliably present on the GenericsType's inner
ClassNode, so the suppression path is a no-op in practice today; the contract form is the
working interface. The matcher handles inner-class annotation names by stripping the segment
after the last {@code $}, so a {@code C.NonNull} (which Groovy renders as {@code C$NonNull})
matches the same as a top-level {@code NonNull} — should the upstream parser start surfacing
the annotations, this slice picks them up without further changes.

**Known limits.**

- **Annotation surfacing** — see above. The infrastructure is in place; the AST input isn't
  consistently there. Out of our hands until Groovy preserves type-use annotations on generic
  type arguments at the StaticTypeChecking phase.
- **No nullity tracking through writes.** {@code xs[i] = null} / {@code xs[i] = something} does
  not currently update the per-element nullity array — the oracle is read-only in this slice.
  Practical impact: a body that *assigns* into the list and then dereferences would still flag
  the dereference. Adding the write-side is a follow-up paralleling the existing per-store
  {@code count} law.
- **No cross-call propagation.** A method receiving a {@code List<String>} returned by another
  contracted method doesn't know whether that other method's @Ensures said anything about
  element nullity. Element-level @Ensures shapes ({@code @Ensures({ result[0] != null })}) are
  encodable in contracts already; they just aren't currently summarised through inter-procedural
  Phase-7 reasoning the way scalar postconditions are.

## Phase 38 — Immutable container factory recognition  *(shipped)*

**Peephole, not theory.** Immutable factories are the easiest immutability slice to land: their
size is known statically, their elements are known statically, and they can never be mutated —
so every {@code .size()}/{@code .contains}/{@code .get} call on a factory receiver can be folded
to a ground SMT term *without* minting a set/list/map handle. There's no new oracle, no per-store
update law, and no quantifier. Just literal-driven folding.

**Recognised receivers.** {@code factoryContainerFor} matches:

- {@code List.of(args)}, {@code Set.of(args)}, {@code Map.of(k1, v1, …)} — Java-9+ factories.
- Groovy list literals {@code [a, b, c]} (kind {@code list} by default; the outer cast
  {@code [a, b, c] as Set} switches the kind via {@code CastExpression} unwrapping).
- Groovy map literals {@code [k1: v1, k2: v2]} via {@code MapEntryExpression} iteration.

**The folds.** For a recognised {@code FactoryContainer} {@code f}:

| Op | Fold |
|---|---|
| {@code f.size()} | {@code intLit(f.entryCount())} |
| {@code f.isEmpty()} | {@code boolLit(f.entryCount() == 0)} |
| {@code f.contains(x)} | {@code x == a_0 ∨ x == a_1 ∨ …} (list/set kinds) |
| {@code f.containsKey(k)} | same disjunction over {@code f.keys} (map kind) |
| {@code f.containsValue(v)} | same disjunction over {@code f.values} (map kind) |
| {@code x in f} | same as {@code f.contains(x)} for list/set; {@code f.containsKey(x)} for map (matches Groovy semantics) |
| {@code f.get(literal_i)} | {@code translate(f.args[i])} (list); {@code ite}-chain over {@code (k_j, v_j)} entries (map) |
| {@code f[literal_i]} | same fold via {@code translateBinary}'s LEFT_SQUARE_BRACKET path |

```groovy
class C {
    @Ensures({ result == 3 })
    static int f() { List.of(1, 2, 3).size() }

    @Ensures({ result == 1 })
    static int g() { List.of(1, 2, 3).contains(2) ? 1 : 0 }

    @Ensures({ result == 20 })
    static int h() { [10, 20, 30][1] }

    @Ensures({ result == 2 })
    static int i() { Map.of("a", 1, "b", 2).get("b") }
}
```

All four verify. Replace {@code result == 3} with {@code result == 4} and the soundness anchor
kicks in: the literal fold means Z3 sees {@code 3 == 4} on the residual goal, refutes immediately.

**Known limits.**

- **No local-variable propagation.** {@code List<Integer> xs = List.of(1, 2, 3); xs.size()}
  doesn't fold — {@code xs} becomes an ordinary list local whose size oracle is unconstrained
  past the assignment. Threading the factory through the {@code Assign} step (parallel to
  Phase 35's materialised-set path) is the natural follow-up.
- **Set.of uniqueness is not enforced.** {@code Set.of(1, 1, 1).size() == 3} folds to true,
  which is technically unsound (the runtime call throws {@code IllegalArgumentException} for
  duplicates and the runtime set has size 1). Dedup-aware sizing would need a static distinct-
  pairs analysis on the literal args; skipped because real code that calls Set.of with
  duplicates is itself a bug.
- **No {@code Collections.unmodifiableX} or {@code .asImmutable()}.** Those wrap an existing
  container — the result inherits its size from the operand, which the size oracle already
  models for named operands; folding would require recognising the wrap explicitly. Out of
  scope for this slice.
- **No {@code .values()} / {@code .keySet()} forwarding.** A factory map's {@code .values()}
  could in principle yield a recognised set factory of the values, composing with downstream
  {@code .contains}. Not wired here — most contracts that care about map values do so via
  {@code containsValue}, which already folds.
- **{@code .get(non-constant-i)} skips honestly.** Folding for a symbolic index would emit an
  {@code ite}-chain plus an explicit out-of-bounds handling; deferred to the same slice that
  threads factories through assignment.

## Non-goals

Things deliberately not pursued, because they don't pay back:

- **Soundness as a hard property.** This is *loud unsoundness*: everything
  outside the fragment emits a "skipped: outside fragment" diagnostic, which is
  honest. Chasing actual soundness would mean rejecting any program that touches
  anything outside the fragment — which is most of them.
- **Orthogonal properties owned by sibling checkers.** Nullness (flow + `@Nullable`/`@NonNull`),
  regular-expression validity, `printf`/`String.format` argument matching, and `@Pure`/side-effect
  compliance are each covered by a dedicated `groovy-typecheckers` extension (`NullChecker`,
  `RegexChecker`, `FormatStringChecker`, `PurityChecker`/`ModifiesChecker`). They ride the same
  `@TypeChecked(extensions = …)` SPI and compose with this one, so groovy-verify stays focused on
  *functional* (contract + arithmetic + array/quantifier) verification rather than reimplementing
  them. Two relate directly: `NullChecker` is the annotation-driven specialist where our nullity
  oracle is a by-product (see the README's "Relationship to Groovy's other checkers"), and
  `PurityChecker`/`ModifiesChecker` can verify the purity our pure-function evaluation (Phase 8a) and
  `@Modifies` framing (Phase 13) assume.
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
  seconds to a compile. The in-process VC cache is shipped (see
  [Phase 34](#phase-34--vc-cache--shipped)) and currently rebates ~18 % at suite
  scale; a `-PverifyEnabled=true`-style "verify only" configuration and a
  persistent disk cache keyed on class-file digests remain as further levers.
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
